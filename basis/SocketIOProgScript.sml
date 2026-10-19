(*
  Module for socket I/O: Unix domain stream sockets and Linux raw packet
  sockets, through the socket FFI in basis_ffi.c.
*)
Theory SocketIOProg
Ancestors
  ml_translator SexpProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib
  semanticPrimitivesSyntax

val _ = translation_extends "SexpProg";

val _ = ml_prog_update (open_module "SocketIO");

val _ = ml_prog_update open_local_block;

(* A socket is its descriptor, as the 8-byte string the FFI expects, together
   with the byte array used for FFI communication on that socket: 4 header
   bytes followed by the data. Every operation reports its status in byte 0. *)
Quote add_cakeml:
  datatype socket = Socket string byte_array
End

Quote add_cakeml:
  fun get_sock s = case s of Socket d b => d
  fun get_buff s = case s of Socket d b => b
  fun get_cap s = case s of Socket d b => Word8Array.length b - 4
End

(* 4 and 8 byte integers, in the same big-endian layout as Marshalling.n2w2 *)
Quote add_cakeml:
  fun n2w8 n bytes off =
    let fun n2w8_aux i n =
      if i < 0 then ()
      else (Word8Array.update bytes (off + i) (Word8.fromInt n);
            n2w8_aux (i - 1) (n div 256))
    in n2w8_aux 7 n end
  fun w82n bytes off =
    let fun w82n_aux i acc =
      if i = 8 then acc
      else w82n_aux (i + 1) (acc * 256 + Word8.toInt (Word8Array.sub bytes (off + i)))
    in w82n_aux 0 0 end
  fun n2w4 n bytes off =
    let fun n2w4_aux i n =
      if i < 0 then ()
      else (Word8Array.update bytes (off + i) (Word8.fromInt n);
            n2w4_aux (i - 1) (n div 256))
    in n2w4_aux 3 n end
End

(* integers as the fixed-width strings that go into the FFI's c argument *)
Quote add_cakeml:
  fun int_string8 n =
    let val b = Word8Array.array 8 (Word8.fromInt 0)
    in (n2w8 n b 0; Word8Array.substring b 0 8) end
  fun int_string2 n =
    let val b = Word8Array.array 2 (Word8.fromInt 0)
    in (Marshalling.n2w2 n b 0; Word8Array.substring b 0 2) end
  fun status b = Word8.toInt (Word8Array.sub b 0)
End

(* Buffer sizes are forced into 1024 <= size <= 65535, the largest count the
   FFI's 2-byte length fields can carry. *)
Quote add_cakeml:
  fun new_buffer bsize =
    Word8Array.array (min 65539 (max (bsize + 4) 1028)) (Word8.fromInt 0)
End

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (add_dec
  ``Dtabbrev NoLocs [] «socket» (Atapp [] (Short «socket»))`` I);

(* SocketError: the operating system refused or failed the operation.
   IllegalArgument: a count or size does not fit the socket's buffer. *)
Quote add_cakeml:
  exception SocketError;
  exception IllegalArgument
End

val _ = ml_prog_update open_local_block;

val SocketError = get_exn_conv ``«SocketError»``
val IllegalArgument = get_exn_conv ``«IllegalArgument»``

Definition SocketError_exn_def:
  SocketError_exn v = (v = Conv (SOME ^SocketError) [])
End

Definition IllegalArgument_exn_def:
  IllegalArgument_exn v = (v = Conv (SOME ^IllegalArgument) [])
End

(* sendi: calls #(unix_socket_write) until something is written or the
   operating system fails the call, and returns the number of bytes written.
   send_all: keeps writing until the whole (specified part of the) buffer is
   written. Both mirror writei and write in TextIO. *)
Quote add_cakeml:
  fun sendi fd b n i =
    let val a = Marshalling.n2w2 n b 0
        val a = Marshalling.n2w2 i b 2
        val a = #(unix_socket_write) fd b in
        if status b <> 0 then raise SocketError
        else
          let val nw = Marshalling.w22n b 1 in
            if nw = 0 then sendi fd b n i
            else nw
          end
    end
  fun send_all fd b n i =
    if n = 0 then () else
      let val nw = sendi fd b n i in
        if nw < n then send_all fd b (n - nw) (i + nw) else () end
End

Quote add_cakeml:
  fun send_aux sock s i z =
    if z <= i then () else let
      val b = get_buff sock
      val cap = get_cap sock
      val left = z - i
      val n = if left <= cap then left else cap
      val _ = Word8Array.copyVec s i n b 4
      val _ = send_all (get_sock sock) b n 0
    in send_aux sock s (i + n) z end
End

(* sends the frame in the socket's buffer with the given FFI call *)
Quote add_cakeml:
  fun load_frame sock frame =
    let val b = get_buff sock
        val n = String.size frame in
      if n <= 0 orelse get_cap sock < n then raise IllegalArgument
      else (Marshalling.n2w2 n b 0; Marshalling.n2w2 0 b 2;
            Word8Array.copyVec frame 0 n b 4; n)
    end
End

(* reads nfds poll results, 2 bytes each, from offset 8 of the poll buffer *)
Quote add_cakeml:
  fun revents_aux b nfds i =
    if i = nfds then []
    else Marshalling.w22n b (8 + 2 * i) :: revents_aux b nfds (i + 1)
End

(* the FFI reports the interface index or MTU in bytes 1 to 8 *)
Quote add_cakeml:
  fun interface_query ffi sock name =
    let val b = get_buff sock
        val _ = ffi (get_sock sock ^ name ^ String.str (Char.chr 0)) b in
      if status b = 0 then w82n b 1 else raise SocketError
    end
End

Quote add_cakeml:
  fun set_kernel_buffer sock size which =
    let val b = get_buff sock
        val c = get_sock sock ^ int_string8 size ^ String.str (Char.chr which)
        val _ = #(set_socket_buffer_size) c b in
      if status b = 0 then w82n b 1 else raise SocketError
    end
End

val _ = ml_prog_update open_local_in_block;

(* Unix domain stream sockets *)

(* listenSetBufferSize path bsize: a listening socket bound to the file path,
   with a buffer of bsize bytes for the data of each transfer. A stale socket
   file at the path is replaced. *)
Quote add_cakeml:
  fun listenSetBufferSize path bsize =
    let val b = new_buffer bsize
        val _ = #(unix_socket_listen) (path ^ String.str (Char.chr 0)) b in
      if status b = 0 then Socket (Word8Array.substring b 1 8) b
      else raise SocketError
    end
End

Quote add_cakeml:
  fun listen path = listenSetBufferSize path 65535
End

(* accept sock: blocks until a client connects to the listening socket, and
   returns the connected socket, with a buffer of the same size. *)
Quote add_cakeml:
  fun accept sock =
    let val b = get_buff sock
        val _ = #(unix_socket_accept) (get_sock sock) b in
      if status b = 0
      then Socket (Word8Array.substring b 1 8) (new_buffer (get_cap sock))
      else raise SocketError
    end
End

(* recv sock n: blocks until data arrives and returns at most n bytes of it.
   The empty string means the peer closed the connection. *)
Quote add_cakeml:
  fun recv sock n =
    let val b = get_buff sock in
      if n <= 0 orelse get_cap sock < n then raise IllegalArgument
      else
        let val _ = Marshalling.n2w2 n b 0
            val _ = #(unix_socket_read) (get_sock sock) b
            val s = status b in
          if s = 0 then Word8Array.substring b 4 (Marshalling.w22n b 1)
          else if s = 2 then ""
          else raise SocketError
        end
    end
End

(* send sock s: writes the whole string, however long. *)
Quote add_cakeml:
  fun send sock s = send_aux sock s 0 (String.size s)
End

(* close sock: closes any kind of socket. *)
Quote add_cakeml:
  fun close sock =
    let val b = get_buff sock
        val _ = #(raw_socket_close) (get_sock sock) b in
      if status b = 0 then () else raise SocketError
    end
End

(* Linux raw packet sockets: whole Ethernet frames on a network interface *)

(* rawSocketSetBufferSize bsize: a raw socket receiving every protocol, with
   a buffer of bsize bytes for one frame. The buffer bounds the frame size
   for rawRecv, rawSend and rawSendTo. *)
Quote add_cakeml:
  fun rawSocketSetBufferSize bsize =
    let val b = new_buffer bsize
        val _ = #(raw_socket_create) "" b in
      if status b = 0 then Socket (Word8Array.substring b 1 8) b
      else raise SocketError
    end
End

Quote add_cakeml:
  fun rawSocket () = rawSocketSetBufferSize 65535
End

(* ifIndex sock name, ifMtu sock name: the index and MTU of the named
   network interface. The socket is only used to ask the operating system. *)
Quote add_cakeml:
  fun ifIndex sock name =
    interface_query (fn c => fn b => #(get_interface_index) c b) sock name
  fun ifMtu sock name =
    interface_query (fn c => fn b => #(get_interface_mtu) c b) sock name
End

(* rawBind sock index: binds the raw socket to the interface with the index,
   so that it receives frames from that interface only. *)
Quote add_cakeml:
  fun rawBind sock index =
    let val b = get_buff sock
        val _ = #(raw_socket_bind) (get_sock sock ^ int_string8 index) b in
      if status b = 0 then () else raise SocketError
    end
End

(* rawRecv sock n: blocks until a frame arrives on the bound socket and returns
   it, or None if the frame was longer than n bytes and had to be dropped. *)
Quote add_cakeml:
  fun rawRecv sock n =
    let val b = get_buff sock in
      if n <= 0 orelse get_cap sock < n then raise IllegalArgument
      else
        let val _ = Marshalling.n2w2 n b 0
            val _ = #(raw_socket_recv) (get_sock sock) b
            val s = status b in
          if s = 0 then Some (Word8Array.substring b 4 (Marshalling.w22n b 1))
          else if s = 2 then None
          else raise SocketError
        end
    end
End

(* rawSend sock frame: sends one frame on the interface the socket is bound
   to. rawSendTo sock index frame: sends it on the interface with the index. *)
Quote add_cakeml:
  fun rawSend sock frame =
    let val n = load_frame sock frame
        val b = get_buff sock
        val _ = #(raw_socket_send) (get_sock sock) b in
      if status b = 0 andalso Marshalling.w22n b 1 = n then ()
      else raise SocketError
    end
  fun rawSendTo sock index frame =
    let val n = load_frame sock frame
        val b = get_buff sock
        val _ = #(raw_socket_sendto) (get_sock sock ^ int_string8 index) b in
      if status b = 0 andalso Marshalling.w22n b 1 = n then ()
      else raise SocketError
    end
End

(* setRecvBufferSize sock size, setSendBufferSize sock size: asks the
   operating system for a receive or send buffer of size bytes on the socket,
   and returns the size it actually set. *)
Quote add_cakeml:
  fun setRecvBufferSize sock size = set_kernel_buffer sock size 0
  fun setSendBufferSize sock size = set_kernel_buffer sock size 1
End

(* Waiting on several sockets *)

(* The events to wait for and the events reported, combined by addition. *)
Quote add_cakeml:
  val pollIn = 1;
  val pollOut = 4;
  val pollErr = 8;
  val pollHup = 16;
  val pollNval = 32
End

(* poll socks timeout: blocks until an event happens on one of the sockets,
   each paired with the events to wait for, or until timeout milliseconds
   have passed. A negative timeout waits forever. Returns None on timeout,
   otherwise the events reported for each socket, in the same order. *)
Quote add_cakeml:
  fun poll socks timeout =
    let val nfds = List.length socks
        val b = Word8Array.array (8 + 2 * nfds) (Word8.fromInt 0)
        val c = String.concat
                  (List.map (fn (sock, ev) => get_sock sock ^ int_string2 ev) socks)
        val _ = n2w4 nfds b 0
        val _ = n2w4 timeout b 4
        val _ = #(raw_socket_poll) c b
        val s = status b in
      if s = 0 then Some (revents_aux b nfds 0)
      else if s = 2 then None
      else raise SocketError
    end
End

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);
