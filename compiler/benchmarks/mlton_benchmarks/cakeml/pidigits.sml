fun print _ = ()

structure Stream =
struct
   datatype 'a u = Nil | Cons of 'a * (unit -> 'a u)
   type 'a t = unit -> 'a u

   fun unfold f =
      let
         fun loop b () =
            case f b of
               None => Nil
             | Some p => case p of (x,b) => (Cons x (loop b))
      in
         loop
      end

   fun map f =
      unfold (fn s =>
              case s () of
                 Nil => None
               | Cons x xs => Some (f x, xs))

end

structure PiDigits =
struct
   fun stream next
              safe
              prod
              cons =
      let
         fun loop z s () =
            let
               val y = next z
            in
               if safe z y
                  then Stream.Cons y (loop (prod z y) s)
               else (case s () of
                        Stream.Nil => Stream.Nil
                      | Stream.Cons x xs => loop (cons z x) xs ())
            end
      in
         loop
      end

   type lft = (int * int * int * int)

   val unit = (1,0,0,1)

   fun comp (q,r,s,t) (u,v,w,x) = (q*u+r*w, q*v+r*x, s*u+t*w, s*v+t*x)

   val pi =
      let
         val init = unit
         val lfts = Stream.map (fn k => (k, 4*k+2, 0, 2*k+1)) (Stream.unfold (fn i => Some(i, i+1)) 1)
         fun floor_extr (q,r,s,t) x = (q * x + r) div (s * x + t)
         fun next z = floor_extr z 3
         fun safe z n = n = floor_extr z 4
         fun prod z n = comp (10, ~10*n, 0, 1) z
         fun cons z z' = comp z z'
      in
         stream next safe prod cons init lfts
      end
end

exception Empty

structure MainShootout =
struct
   fun display n =
      let
         fun loop (ds, (k, col)) =
            if k < n
               then let
                       val col =
                          if col = 10
                             then (print "\t:"; print (Int.toString k); print "\n";
                                   1)
                          else col + 1
                    in
                       case ds () of
                          Stream.Nil => raise Empty
                        | Stream.Cons d ds =>
                             (print (Int.toString d);
                              loop (ds, (k + 1, col)))
                    end
            else (print (String.implode(List.tabulate (10 - col) (fn _ => #" ")));
                  print "\t:"; print (Int.toString k); print "\n";
                  ())
      in
         loop (PiDigits.pi, (0, 0))
      end
   (*fun usage name =
      (TextIO.output (TextIO.stdErr,
                      concat ["usage: ", OS.Path.file name, " <n>\n"]);
       OS.Process.failure)
   fun main (name, arguments) =
      case arguments of
         [n] => (case Int.fromString n of
                    Some n => if n >= 1
                                 then (display n; OS.Process.success)
                              else usage name
                  | None => usage name)
       | _ => usage name*)
end

(*
val _ = OS.Process.exit (Main.main (CommandLine.name (), CommandLine.arguments ()))
*)

structure Main =
struct
   fun display n =
      let
         fun loop (ds, k, n) =
            case ds () of
               Stream.Nil => raise Empty
             | Stream.Cons d ds =>
                  if d = 0
                     then if n = 0
                             then (print (Int.toString k); print "\n")
                          else loop (ds, k + 1, n - 1)
                  else loop (ds, k + 1, n)
      in
         loop (PiDigits.pi, 0, n)
      end
   (*fun usage name =
      (TextIO.output (TextIO.stdErr,
                      concat ["usage: ", OS.Path.file name, " <n>\n"]);
       OS.Process.failure)
   fun main (name, arguments) =
      case arguments of
         [n] => (case IntInf.fromString n of
                    Some n => if n >= 1
                                 then (display n; OS.Process.success)
                              else usage name
                  | None => usage name)
       | _ => usage name*)

   val doit = display
end

val foo = Main.doit 500;
