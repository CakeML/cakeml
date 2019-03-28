(* Written by Henry Cejtin (henry@sourcelight.com). *)
fun print _ = ();

signature MATRIX =
   sig
      type 'entry matrix
      val make: int * int * (int * int -> 'entry) -> 'entry matrix
      val height: 'entry matrix -> int
      val width: 'entry matrix -> int
      val fetch: 'entry matrix * int * int -> 'entry
      val fetchRow: 'entry matrix * int -> int -> 'entry
      val fetchCol: 'entry matrix * int -> int -> 'entry
      val store: 'entry matrix * int * int * 'entry -> unit
      val storeRow: 'entry matrix * int -> int * 'entry -> unit
      val storeCol: 'entry matrix * int -> int * 'entry -> unit
      val rowSwap: 'entry matrix * int * int -> unit
      val colSwap: 'entry matrix * int * int -> unit
      val rowOp: 'entry matrix * int * int * ('entry * 'entry -> 'entry) -> unit
      val colOp: 'entry matrix * int * int * ('entry * 'entry -> 'entry) -> unit
      val copy: 'entry matrix -> 'entry matrix
      val map: 'entry1 matrix * ('entry1 -> 'entry2) -> 'entry2 matrix
      val toString: 'entry matrix * ('entry -> string) -> string
   end

structure Matrix:> MATRIX =
   struct
      type 'entry matrix = int * int * 'entry array

      exception sizeError

      exception index

      exception foldError

      fun make (height: int, width: int, generator: int * int -> 'entry)
         : 'entry matrix =
         if height < 0 orelse width < 0
            then raise sizeError
         else (height,
               width,
               Array.tabulate (height*width,
                               fn z => generator (z div width,
                                                  z mod width)))

      fun height (height, _, _) = height

      fun width (width, _, _) = width

      fun fetch ((height, width, mat), row, col) =
         if 0 <= row
            andalso row < height
            andalso 0 <= col
            andalso col < width
            then Array.sub (mat, col + width*row)
         else raise index

      fun fetchRow ((height, width, mat), row) =
         if 0 <= row andalso row < height
            then let val offset = width * row
                 in fn col =>
                    if 0 <= col andalso col < width
                       then Array.sub (mat, col + offset)
                    else raise index
                 end
         else raise index

      fun fetchCol ((height, width, mat), col) =
         if 0 <= col andalso col < width
            then fn row =>
               if 0 <= row andalso row < height
                  then Array.sub (mat, col + width*row)
               else raise index
         else raise index

      fun store ((height, width, mat), row, col, entry) =
         if 0 <= row
            andalso row < height
            andalso 0 <= col
            andalso col < width
            then Array.update (mat, col + width*row, entry)
         else raise index

      fun storeRow ((height, width, mat), row) =
         if 0 <= row andalso row < height
            then let val offset = width * row
                 in fn (col, entry) =>
                    if 0 <= col andalso col < width
                       then Array.update (mat, col + offset, entry)
                    else raise index
                 end
         else raise index

      fun storeCol ((height, width, mat), col) =
         if 0 <= col andalso col < width
            then fn (row, entry) =>
               if 0 <= row andalso row < height
                  then Array.update (mat, col + width*row, entry)
               else raise index
         else raise index

      fun swapLoop (from1: int -> 'entry,
                    to1: int * 'entry -> unit,
                    from2: int -> 'entry,
                    to2: int * 'entry -> unit,
                    limit: int): unit =
         let fun loop (i: int): unit =
            if i = limit
               then ()
            else let val tmp = from1 i
                 in to1 (i, from2 i);
                    to2 (i, tmp);
                    loop (i + 1)
                 end
         in loop 0
         end

      fun rowSwap (mat as (height, width, _), row1, row2): unit =
         if 0 <= row1 andalso row1 < height
            andalso 0 <= row2 andalso row2 < height
            then if row1 = row2
                    then ()
                 else swapLoop (fetchRow (mat, row1),
                                storeRow (mat, row1),
                                fetchRow (mat, row2),
                                storeRow (mat, row2),
                                width)
         else raise index

      fun colSwap (mat as (height, width, _), col1, col2): unit =
         if 0 <= col1 andalso col1 < width
            andalso 0 <= col2 andalso col2 < width
            then if col1 = col2
                    then ()
                 else swapLoop (fetchCol (mat, col1),
                                storeCol (mat, col1),
                                fetchCol (mat, col2),
                                storeCol (mat, col2),
                                height)
         else raise index

      fun opLoop (from1: int -> 'entry,
                  from2: int -> 'entry,
                  to2: int * 'entry -> unit,
                  limit: int,
                  f: 'entry * 'entry -> 'entry): unit =
         let fun loop (i: int): unit =
            if i = limit
               then ()
            else (
                  to2 (i,
                       f (from1 i, from2 i));
                  loop (i + 1))
         in loop 0
         end

      fun rowOp (mat as (height, width, _),
                 row1,
                 row2,
                 f: 'entry * 'entry -> 'entry): unit =
         if 0 <= row1 andalso row1 < height
            andalso 0 <= row2 andalso row2 < height
            andalso row1 <> row2
            then opLoop (fetchRow (mat, row1),
                         fetchRow (mat, row2),
                         storeRow (mat, row2),
                         width,
                         f)
         else raise index

      fun colOp (mat as (height, width, _),
                 col1,
                 col2,
                 f: 'entry * 'entry -> 'entry): unit =
         if 0 <= col1 andalso col1 < width
            andalso 0 <= col2 andalso col2 < width
            andalso col1 <> col2
            then opLoop (fetchCol (mat, col1),
                         fetchCol (mat, col2),
                         storeCol (mat, col2),
                         height,
                         f)
         else raise index

      fun copy ((height, width, mat)) =
         (height,
          width,
          Array.tabulate (Array.length mat,
                          fn i => Array.sub (mat, i)))

      fun map ((height, width, mat: 'entry1 Array.array),
               f: 'entry1 -> 'entry2)
         : 'entry2 matrix =
         (height,
          width,
          Array.tabulate (Array.length mat,
                          fn i => f (Array.sub (mat, i))))

      (* Natural fold a range of integers in reverse. *)
      fun naturalFold (limit: int,
                       state: 'state,
                       folder: int * 'state -> 'state): 'state =
         let fun loop (i: int, state: 'state) =
            if i = 0
               then state
            else loop (i - 1, folder (i - 1, state))
         in if limit < 0
               then raise foldError
            else loop (limit, state)
         end


      local val blank8 = Byte.charToByte #" "

         fun makeBlanks size =
            let val blanks = Word8Vector.tabulate (size,
                                                   fn _ => blank8)
            in Byte.bytesToString blanks
            end

      in fun toString (mat: 'entry matrix, f: 'entry -> string): string =
         let val mat as (height, width, _) = map (mat, f)
            fun maxSize from (i, width) = Int.max (String.size (from i),
                                                   width)
            fun colWidth col = naturalFold (height,
                                            0,
                                            maxSize (fetchCol (mat,
                                                               col)))
            val widths = Vector.tabulate (width, colWidth)
            fun doRow (row: int, ac: string list): string list =
               let val from = fetchRow (mat, row)
                  fun loop (col: int, ac: string list) =
                     let val next = from col
                        val ac = next::ac
                        val s = String.size next
                        val pad = Vector.sub (widths, col) - s
                        val ac = if pad <= 0
                                    then ac
                                 else (makeBlanks pad)::ac
                     in if col = 0
                           then ac
                        else loop (col - 1,
                                   " "::ac)
                     end
                  val ac = "\n"::ac
               in if width = 0
                     then ac
                  else loop (width - 1, ac)
               end
            val pieces = naturalFold (height,
                                      [],
                                      doRow)
         in String.concat pieces
         end
      end
   end

val zero = IntInf.fromInt 0

fun smaller (a: IntInf.int, b: IntInf.int): bool =
   (not (a = zero))
   andalso (b = zero orelse IntInf.< (IntInf.abs a , IntInf.abs b))

fun smithNormalForm (mat: IntInf.int Matrix.matrix): IntInf.int Matrix.matrix =
   let val height = Matrix.height mat
      val width = Matrix.width mat
      val mat = Matrix.copy mat
      val range = Int.min (width, height)
      fun dd pos =
         let val matCol = Matrix.fetchCol (mat, pos)
            val matRow = Matrix.fetchRow (mat, pos)
            val _ = print ("dd: pos = " ^ (Int.toString pos) ^ "\n")
            fun swapRowLoop (best, bestRow, bestCol, row) =
               if row >= height
                  then (Matrix.rowSwap (mat, pos, bestRow);
                        Matrix.colSwap (mat, pos, bestCol))
               else let val matRow = Matrix.fetchRow (mat, row)
                        fun swapColLoop (best, bestRow, bestCol, col) =
                           if col >= width
                              then swapRowLoop (best, bestRow, bestCol, row + 1)
                           else let val next = matRow col
                                in if smaller (next, best)
                                      then swapColLoop (next, row, col, col + 1)
                                   else swapColLoop (best, bestRow, bestCol, col + 1)
                                end
                    in swapColLoop (best, bestRow, bestCol, pos)
                    end
            fun rowLoop row =
               if row < height
                  then if (matCol row) = zero
                          then rowLoop (row + 1)
                       else (Matrix.rowOp (mat,
                                           pos,
                                           row,
                                           let val x = IntInf.~ (IntInf.quot(matCol row, matCol pos))
                                           in fn (lhs, rhs) => IntInf.+ (IntInf.* (lhs, x), rhs)
                                           end);
                             if (matCol row) = zero
                                then rowLoop (row + 1)
                             else hitPosAgain ())
               else let fun colLoop col =
                  if col < width
                     then if (matRow col) = zero
                             then colLoop (col + 1)
                          else (Matrix.colOp (mat,
                                              pos,
                                              col,
                                              let val x = IntInf.~ (IntInf.quot (matRow col, matRow pos))
                                              in fn (lhs, rhs) => IntInf.+ (IntInf.* (lhs, x), rhs)
                                              end);
                                if (matRow col) = zero
                                   then colLoop (col + 1)
                                else hitPosAgain ())
                  else ()
                    in colLoop (pos + 1)
                    end
            and hitPosAgain () = (swapRowLoop (zero, pos, pos, pos);
                                  rowLoop (pos + 1))
         in hitPosAgain ()
         end
      fun loop pos =
         if pos = range
            then mat
         else (dd pos;
               loop (pos + 1))
   in loop 0
   end

val table = [[ 8,  ~3,   1,   3,   6,   9,  ~2,   4,  ~9,  ~9,   2,   3,   8,  ~1,   3,  ~5,   4,  ~3,  ~5,  ~6,   8,   1,   4,  ~5,   7,  ~4,  ~4,  ~7,   7,   1,   4,  ~3,   8,   4,  ~4,  ~8,   5,  ~9,   3,  ~4,   1,   9,  ~8,  ~6,  ~2,   8,  ~9,  ~5,  ~3,  ~3],
             [ 0,   8,  ~6,  ~2,  ~3,   4,   5,  ~2,   7,  ~7,  ~6,  ~7,  ~3,  ~4,   9,   7,  ~3,   3,   0,   3,   3,  ~8,  ~8,   2,   3,   8,   3,  ~2,  ~4,   3,  ~6,  ~6,  ~2,   6,   5,  ~1,  ~3,   1,   8,  ~8,   2,   1,  ~7,  ~7,  ~7,  ~3,  ~6,   6,  ~4,  ~9],
             [ 0,  ~5,   8,  ~9,   2,   4,   2,   7,  ~4,   9,  ~3,   6,  ~2,   3,  ~3,   0,  ~9,   5,   8,  ~1,   2,  ~8,   3,   4,  ~6,   5,  ~6,  ~5,  ~8,   0,  ~5,   3,  ~2,  ~5,   8,   7,  ~1,   1,  ~1,   7,   6,   3,   6,   5,   6,   8,   7,   9,   7,  ~3],
             [ 5,   4,   7,   2,   3,  ~9,   7,  ~7,   3,  ~8,   7,   5,   5,  ~2,  ~6,  ~3,   6,   5,   3,  ~1,  ~1,   4,   5,  ~5,   5,   9,   9,   3,   8,  ~3,  ~1,   9,  ~9,   6,  ~7,   7,   4,   6,  ~8,  ~9,   0,  ~3,  ~2,  ~7,   1,  ~2,  ~6,   7,   7,   7],
             [ 2,   9,   9,   3,  ~4,   0,   9,   2,   5,   3,  ~5,  ~3,  ~1,   1,   8,  ~6,   2,  ~4,  ~8,  ~7,  ~8,   4,   5,   8,  ~1,  ~1,   7,   2,   5,   5,  ~4,  ~7,  ~3,  ~7,   6,  ~4,  ~5,  ~8,  ~5,  ~9,  ~8,   5,  ~5,  ~5,   0,   8,   8,   6,   4,  ~1],
             [ 5,   5,   1,  ~7,   3,  ~5,   4,   9,   3,   4,   4,  ~5,   7,  ~1,   7,   4,  ~7,   7,  ~7,  ~2,   9,  ~9,   0,  ~4,  ~4,   0,   2,   6,   3,  ~1,   6,   6,   8,  ~6,  ~4,  ~9,   3,  ~2,  ~5,   5,  ~3,   2,  ~1,  ~6,   9,   3,  ~3,  ~8,  ~9,   7],
             [ 7,   1,   2,   7,   6,   5,  ~6,  ~3,  ~4,  ~8,   0,   9,   6,   1,   2,  ~5,   4,   4,   4,  ~6,  ~7,  ~9,  ~6,   2,  ~4,   5,  ~2,   1,   0,   1,  ~8,   7,  ~7,  ~5,   4,   1,  ~5,   4,  ~4,  ~2,  ~3,   1,   1,   3,   4,  ~4,  ~5,   9,   8,  ~2],
             [ 6,   2,  ~1,  ~8,   4,  ~7,   7,  ~3,  ~2,  ~5,   3,   0,   3,  ~9,   3,   3,   9,  ~1,   4,   8,  ~9,   6,  ~5,   9,   5,  ~1,  ~1,  ~9,   7,  ~2,   3,   9,   8,   9,   2,   7,   7,   6,  ~1,  ~1,  ~2,  ~2,  ~7,   3,  ~6,   0,  ~9,   4,   3,   7],
             [ 0,  ~6,  ~3,  ~7,  ~1,   5,  ~2,   8,  ~5,  ~3,  ~8,   7,  ~2,  ~2,   0,  ~8,   4,   8,   9,  ~5,  ~4,  ~8,  ~1,   7,   1,   1,   6,  ~9,  ~4,   0,   8,   4,   3,  ~7,   6,   0,   1,   8,   6,  ~1,  ~1,  ~7,   9,  ~9,  ~5,  ~2,  ~2,  ~1,   1,   0],
             [~4,   9,   6,  ~3,  ~2,  ~6,  ~3,   4,   8,  ~8,   1,  ~5,   9,   7,   9,   7,  ~9,  ~6,   6,   1,  ~3,   3,  ~3,  ~7,   1,   7,  ~7,   0,  ~2,   7,  ~4,  ~6,   0,   1,  ~3,  ~5,  ~9,  ~7,   8,   4,   9,  ~8,  ~8,  ~7,  ~6,   7,   6,  ~3,  ~8,   5],
             [ 6,   7,  ~5,  ~9,   6,   1,   8,   4,  ~2,   7,  ~7,  ~1,  ~9,   1,  ~6,  ~5,   4,   9,   6,   0,  ~8,  ~3,   1,  ~3,   8,  ~3,   2,   9,  ~3,  ~9,  ~1,  ~3,   4,   3,   2,  ~9,  ~5,  ~3,   8,  ~4,   8,   5,  ~4,   7,   6,  ~8,   7,   6,  ~5,   5],
             [ 1,   7,  ~8,  ~9,  ~7,  ~3,   8,   9,  ~7,  ~1,  ~7,   4,   0,   0,   1,  ~5,   9,  ~8,  ~1,  ~2,   3,   5,   9,  ~9,   5,   4,  ~9,   1,  ~4,  ~2,   3,  ~4,   8,  ~6,  ~4,  ~8,  ~5,  ~5,   4,  ~2,  ~4,  ~1,  ~9,  ~5,   2,  ~9,   2,  ~9,  ~2,  ~3],
             [~5,  ~4,  ~4,   9,   2,   7,  ~2,   6,   7,   2,  ~9,   4,   2,   7,   8,  ~9,   2,   5,   3,   9,   6,   3,   0,  ~7,  ~6,  ~7,   6,  ~2,   9,  ~3,  ~6,   9,  ~9,   2,   2,  ~6,  ~1,   4,  ~3,   3,   0,   6,  ~3,   4,   9,   9,  ~6,   5,   5,  ~5],
             [ 5,  ~7,   8,  ~4,   8,   8,  ~4,  ~9,   6,   0,  ~3,   6,   0,   8,   8,  ~6,  ~2,   5,   4,  ~1,  ~8,   1,  ~3,  ~1,   2,   3,  ~9,  ~9,  ~5,   1,   8,  ~5,  ~3,   0,  ~4,  ~9,   0,  ~6,   3,  ~1,  ~7,   0,   8,   9,  ~6,  ~1,  ~9,   1,  ~6,   2],
             [ 7,  ~5,  ~1,   5,  ~2,   7,   0,  ~7,  ~1,   8,   8,  ~3,   9,  ~5,   7,  ~8,  ~8,  ~4,   3,   2,  ~1,   8,  ~2,   1,   2,   5,   0,  ~6,   7,   3,   3,   7,  ~5,   5,  ~1,   1,   0,  ~8,   1,   0,   0,  ~4,   6,   9,  ~5,  ~6,   3,  ~5,   8,   5],
             [~4,  ~2,   3,  ~3,  ~1,   2,  ~2,  ~1,  ~9,  ~5,   1,   0,   0,   2,   9,  ~3,  ~9,   2,   9,   3,   8,  ~3,   4,   8,   8,   3,  ~3,  ~1,  ~4,   4,  ~6,  ~9,   5,  ~2,   1,   3,  ~7,  ~5,  ~6,  ~5,  ~8,   4,  ~8,  ~3,   5,   0,   7,  ~9,   6,   2],
             [ 5,   1,   4,  ~3,  ~1,  ~9,   5,  ~8,  ~8,   6,   1,   1,  ~2,   7,   5,   6,  ~4,   2,  ~7,   0,  ~7,  ~3,  ~5,   9,   3,   4,  ~6,   8,  ~4,   3,   6,   0,   2,   3,  ~6,   3,   9,   4,   1,  ~4,   6,  ~5,  ~7,   0,  ~1,  ~8,  ~3,  ~9,   9,   7],
             [ 2,  ~6,  ~1,   8,   4,  ~3,  ~1,  ~6,  ~2,  ~8,  ~2,  ~1,  ~1,  ~5,  ~9,  ~8,   9,  ~9,   5,   1,   9,  ~1,  ~6,   9,  ~7,   2,   8,  ~7,   4,  ~9,   7,   6,  ~2,   1,  ~2,  ~7,   8,   0,   5,   0,  ~5,  ~7,  ~6,   0,   4,   0,   3,  ~8,   5,   4],
             [~2,   9,  ~9,  ~6,   1,  ~8,   8,   4,  ~6,   8,   1,  ~3,  ~7,   8,  ~5,   2,  ~8,   1,   3,  ~2,   6,   6,   6,   1,   0,   0,  ~7,   7,  ~3,  ~3,   0,  ~4,   3,  ~7,  ~6,   7,   5,   9,  ~5,   7,  ~8,   2,   3,  ~8,  ~7,   6,  ~5,  ~5,  ~8,  ~9],
             [~7,  ~4,   4,   1,  ~1,  ~3,  ~8,   3,   7,   9,   8,   3,   0,   4,   4,  ~1,  ~5,   4,   2,   2,   0,   6,  ~6,   2,  ~9,   8,  ~9,   3,  ~2,   2,   6,   6,   1,   7,   1,   0,  ~8,   2,   3,  ~3,   8,   9,   5,   5,  ~6,   4,  ~7,  ~4,  ~2,  ~3],
             [~5,   8,   6,   1,  ~6,  ~6,   6,   1,   1,  ~3,  ~9,  ~6,   2,  ~7,   2,  ~1,   6,  ~6,   0,   2,  ~7,   8,  ~8,   4,   9,  ~3,   9,  ~7,  ~9,  ~6,  ~4,  ~4,  ~5,   8,   2,  ~5,  ~4,  ~3,   5,   2,   1,  ~3,  ~3,  ~7,  ~9,   3,   7,  ~7,   3,  ~8],
             [~4,  ~7,  ~2,   2,  ~4,  ~2,   6,  ~3,  ~1,  ~4,   0,  ~5,   9,   7,  ~6,  ~9,   7,  ~9,  ~6,   2,  ~3,   1,   5,  ~9,   4,  ~5,   4,  ~9,   1,  ~2,  ~2,   4,   0,   4,  ~8,  ~8,   3,  ~1,  ~5,  ~4,  ~9,  ~7,   7,   6,   3,  ~9,   6,   4,  ~4,  ~7],
             [~9,   6,   6,  ~5,  ~1,  ~7,   4,  ~9,   4,  ~1,   6,  ~4,   7,   2,   8,   7,   3,   1,  ~7,   7,   7,   9,   8,  ~9,   7,   2,   1,   2,  ~8,   4,   5,   6,   7,   2,  ~7,   6,   8,   4,  ~9,   7,  ~5,   6,   9,  ~1,   9,   2,   0,   9,   3,   6],
             [ 4,  ~3,   8,   0,  ~2,  ~2,   2,  ~3,   8,   3,   1,  ~8,  ~5,  ~2,   5,   6,   8,   0,  ~3,   4,  ~2,   4,  ~9,  ~5,   7,   6,  ~4,  ~7,   2,   4,  ~3,  ~8,  ~9,   9,   8,  ~9,   3,  ~7,   4,  ~7,  ~5,   4,   9,   3,  ~6,  ~3,  ~7,   4,   2,  ~2],
             [~8,  ~8,   6,  ~2,  ~6,   8,  ~3,   3,  ~1,  ~7,   1,   9,   1,   7,  ~6,   8,  ~2,  ~9,  ~1,   3,  ~4,   7,   8,  ~1,   9,  ~9,   6,  ~3,   5,   0,   2,   5,  ~1,  ~6,  ~6,   1,   8,   6,  ~3,  ~9,  ~1,   9,  ~2,   9,  ~8,  ~7,  ~3,   6,  ~3,  ~3],
             [ 5,  ~2,   3,   0,  ~9,  ~8,  ~6,   1,   8,   0,   1,   2,  ~8,  ~2,   0,  ~9,  ~8,   0,   5,  ~3,  ~4,   5,   6,  ~2,  ~5,   0,  ~9,   9,  ~9,  ~5,   9,   9,  ~5,  ~2,   4,   3,   8,  ~8,  ~7,   5,  ~3,  ~2,   2,   3,   9,   7,  ~1,   0,   4,  ~1],
             [~4,   5,  ~5,   7,   8,   9,   7,  ~3,   1,   9,  ~7,  ~1,   8,  ~5,  ~1,   2,  ~8,   1,   0,   9,  ~8,  ~1,   6,  ~1,   9,  ~8,   7,   4,  ~8,   7,   0,  ~6,   2,   3,   7,   4,  ~3,  ~5,   9,  ~3,   0,   6,  ~9,   2,   4,  ~8,   6,  ~7,   9,   1],
             [ 7,   0,  ~9,   6,   8,   2,   2,   5,  ~6,  ~6,   9,  ~5,   9,   2,   2,  ~8,   0,  ~6,  ~9,  ~6,  ~4,  ~9,   8,  ~2,   9,   7,  ~5,  ~1,   7,   2,  ~7,   7,  ~1,  ~3,   6,   6,   1,  ~4,   0,  ~1,  ~6,  ~5,   6,  ~7,  ~3,  ~2,   8,   2,  ~9,   8],
             [ 8,  ~7,  ~9,  ~6,   9,  ~7,  ~7,   6,  ~8,   9,   5,  ~4,   1,  ~7,  ~8,  ~6,  ~3,   8,  ~8,   1,  ~8,   6,   9,  ~3,  ~7,   7,   1,   6,   1,   0,   8,  ~5,  ~8,   8,  ~9,   0,   4,   4,   3,  ~4,   6,  ~3,  ~9,   0,   4,  ~4,  ~5,  ~9,  ~5,  ~8],
             [~3,  ~2,   8,   1,  ~1,  ~1,  ~4,   3,   7,  ~2,  ~9,   9,  ~8,  ~9,   6,  ~4,   7,  ~1,  ~5,  ~3,  ~9,   0,  ~3,   0,   7,   9,   1,  ~2,   7,  ~9,  ~6,   3,   3,  ~4,  ~7,  ~3,  ~4,  ~8,  ~2,  ~3,  ~9,  ~2,  ~6,   3,  ~6,  ~4,   7,  ~5,  ~8,  ~1],
             [~9,  ~9,  ~2,  ~9,  ~9,   9,   6,   6,   7,   5,  ~1,  ~2,   1,   5,   2,  ~3,  ~4,   1,  ~6,   0,  ~3,  ~9,  ~1,   7,   0,  ~9,   5,  ~2,  ~2,   5,   3,   4,  ~1,   6,  ~6,   3,  ~6,   7,  ~1,   5,  ~8,  ~4,  ~2,  ~2,  ~6,  ~5,  ~6,   3,  ~1,   4],
             [ 7,   7,   8,   7,   6,   1,  ~2,   5,  ~6,   9,   4,   8,   5,   0,  ~4,  ~2,  ~2,  ~5,  ~2,  ~6,   9,  ~8,  ~2,  ~5,  ~9,   3,  ~6,  ~3,  ~4,  ~5,  ~2,   6,   1,   6,  ~5,   0,  ~3,  ~2,   4,  ~6,   1,   6,  ~1,   3,  ~9,   2,  ~3,   1,   5,  ~6],
             [ 6,   4,  ~7,   3,  ~7,   9,   1,  ~7,  ~8,   0,  ~6,   8,   4,   1,   9,   6,   8,   3,   0,   9,   0,   4,   9,  ~7,  ~7,   1,   5,   1,  ~5,   6,   9,   2,   4,   1,  ~9,   8,   4,   5,   8,   3,   2,  ~9,  ~6,  ~9,   9,  ~9,   7,  ~6,  ~4,   3],
             [~3,  ~9,  ~4,   2,   3,   9,  ~9,   8,  ~9,   9,  ~4,  ~9,  ~5,   5,   0,   7,   3,  ~5,  ~8,   2,  ~3,   0,  ~9,  ~3,   1,   9,   4,   5,  ~1,   8,   0,  ~4,  ~2,   9,  ~4,  ~1,   3,   5,   9,  ~1,   1,   4,  ~8,  ~2,  ~3,   5,   1,   5,  ~6,   7],
             [ 9,  ~3,   2,  ~9,   3,   4,   0,   7,  ~5,   9,   0,  ~6,   7,  ~2,   3,  ~7,   2,  ~5,  ~2,   6,   3,  ~9,  ~5,  ~9,   5,   2,  ~5,  ~3,   8,  ~5,   6,   2,   9,  ~7,  ~7,  ~7,  ~6,   9,  ~3,   6,   0,   6,  ~6,  ~9,   4,  ~3,  ~9,   0,  ~4,  ~9],
             [~4,  ~8,   8,  ~7,   7,   0,  ~6,  ~6,   8,  ~9,  ~4,   5,  ~3,  ~1,   7,  ~5,  ~6,  ~1,   8,   6,  ~2,   1,  ~1,   5,  ~9,   1,  ~1,  ~7,  ~6,  ~6,  ~6,  ~4,   6,   3,  ~5,  ~5,  ~6,   2,   3,  ~6,  ~8,  ~3,   8,  ~2,  ~5,  ~4,  ~3,   1,   4,  ~4],
             [ 4,  ~6,   2,   6,   2,  ~8,   8,   5,   8,  ~2,   0,  ~6,  ~1,  ~6,  ~2,   2,   6,  ~9,  ~7,  ~6,  ~4,  ~4,  ~7,  ~2,   8,   6,   3,  ~7,  ~6,   8,   2,   3,   4,   5,   3,   4,  ~6,   8,   8,  ~1,   4,  ~5,   6,   2,   8,  ~3,  ~9,  ~2,   6,   7],
             [ 3,  ~4,   0,  ~3,  ~5,   0,  ~2,  ~6,  ~2,   8,   5,  ~9,  ~4,  ~8,  ~6,   0,   8,   9,   1,  ~2,   8,   2,  ~2,   8,   9,   3,   3,   5,  ~9,  ~3,  ~2,   7,   2,   9,   0,   4,   8,  ~9,   0,  ~6,   9,  ~9,   9,  ~4,   8,  ~8,  ~8,   2,  ~3,   2],
             [~1,   3,  ~9,  ~8,  ~7,   6,  ~6,   3,   0,   5,  ~5,   1,   2,  ~2,  ~3,   7,   7,   3,  ~4,  ~2,  ~9,  ~5,  ~1,   9,   6,   8,   2,   8,   7,  ~3,   4,   6,   6,   0,  ~2,   2,  ~7,  ~7,   6,  ~3,   8,   2,   1,   0,   8,  ~1,   3,   9,   8,   6],
             [ 1,  ~2,  ~3,   6,   5,   5,  ~6,  ~4,  ~5,   1,   1,   6,  ~7,  ~4,  ~3,   4,   4,  ~8,  ~9,   7,  ~2,  ~3,  ~7,  ~2,   1,   2,   0,   8,  ~6,  ~5,  ~5,   7,   8,   5,  ~2,   3,   9,   0,   5,   1,   3,  ~4,  ~6,   1,   4,  ~9,  ~2,   5,   4,   3],
             [ 3,   3,   9,  ~2,   6,   9,   4,   9,   4,  ~8,   5,  ~1,   3,  ~2,   1,  ~7,  ~3,   2,   2,   0,  ~3,   3,   8,   2,   0,  ~5,   7,   1,   4,  ~8,   8,  ~9,  ~1,   1,  ~9,  ~4,   5,   2,   2,   8,   6,   1,   6,  ~2,   2,   7,   1,  ~6,  ~1,  ~1],
             [ 4,  ~2,   4,  ~1,  ~5,  ~1,   5,  ~2,   3,  ~4,  ~5,   0,   2,  ~4,   6,   4,  ~3,   2,   2,   5,  ~6,  ~7,  ~9,  ~1,  ~9,  ~9,   6,   0,   6,   5,   9,  ~1,   3,  ~3,  ~8,   8,  ~8,   8,   4,   5,  ~1,  ~5,   1,   0,   3,  ~2,   5,   6,   6,   5],
             [~4,   9,   6,   8,  ~9,   5,   5,  ~3,  ~7,   7,   6,   8,  ~8,   0,   4,  ~1,   9,   5,  ~7,   0,  ~1,  ~2,   3,   6,   0,   4,  ~3,   1,   4,   6,   4,   0,   5,  ~1,   7,  ~7,  ~6,  ~8,  ~3,  ~6,   7,  ~1,  ~3,  ~2,  ~3,  ~5,   3,   1,  ~8,  ~9],
             [~6,   4,  ~5,   9,   9,  ~7,  ~1,  ~8,  ~4,   2,  ~6,   0,  ~6,  ~6,   7,   6,   0,   1,   7,  ~7,   0,  ~4,  ~6,  ~8,  ~9,   5,  ~6,  ~9,   2,  ~7,  ~2,  ~6,   9,   4,  ~5,   0,   4,  ~4,  ~5,   6,   9,   1,  ~6,  ~5,   3,  ~1,   7,  ~7,  ~6,   7],
             [~8,   7,   7,  ~6,   7,  ~4,   8,   0,  ~9,  ~8,  ~3,   7,  ~3,   3,   8,  ~7,  ~2,  ~7,   5,   5,  ~5,   4,   6,   2,   4,   1,   4,  ~9,  ~3,   8,   8,  ~9,  ~4,  ~2,   1,  ~3,   1,   3,   9,  ~5,  ~8,  ~2,   7,   8,   9,   2,   0,   1,  ~9,   6],
             [~7,   1,  ~9,   5,  ~5,  ~5,   7,   6,  ~5,  ~9,  ~6,  ~8,  ~6,   9,   7,   9,   0,  ~5,   7,   7,  ~6,   4,   5,  ~9,  ~1,  ~2,  ~7,   3,  ~5,  ~2,  ~5,   5,  ~3,  ~4,  ~2,  ~8,   2,  ~8,   0,  ~8,   0,  ~8,   9,   8,  ~5,  ~5,   1,   3,   5,  ~4],
             [~8,  ~8,   0,  ~5,  ~8,  ~6,   3,  ~6,  ~4,   6,   1,  ~5,  ~6,  ~8,  ~4,  ~6,  ~2,  ~6,   6,  ~4,   8,   8,   4,  ~5,  ~1,   0,   9,  ~8,  ~3,  ~1,  ~8,   7,  ~3,   0,  ~7,   1,  ~7,  ~1,  ~7,   3,  ~7,   3,  ~4,  ~8,   8,  ~7,  ~9,  ~8,   3,   2],
             [ 3,   6,   8,  ~9,   7,   1,  ~9,   9,   3,   8,   6,   4,  ~2,   1,  ~8,   4,  ~7,  ~4,  ~3,   3,  ~5,  ~6,  ~7,  ~2,   0,  ~4,   5,   2,   5,   6,   3,  ~8,   2,  ~5,  ~7,   6,   8,  ~2,  ~5,  ~4,   9,   9,   2,  ~2,  ~2,   7,   4,   4,  ~2,   3],
             [ 6,   6,  ~5,  ~2,  ~8,  ~2,  ~9,   0,   2,   4,  ~6,  ~9,   9,   0,  ~8,  ~3,  ~1,  ~2,  ~1,   6,   8,   2,  ~9,   5,  ~2,   1,   7,  ~6,   5,   1,  ~1,   4,  ~4,  ~7,  ~6,  ~3,  ~8,   2,   2,   5,   5,  ~6,   5,   3,   3,   7,   4,   7,  ~3,  ~9],
             [~9,   6,  ~4,   1,   3,  ~8,  ~8,  ~8,  ~1,   5,   1,   1,  ~1,   6,   5,   1,  ~1,   5,  ~8,   8,  ~7,  ~5,  ~1,  ~1,   6,  ~8,  ~3,  ~1,  ~2,  ~6,  ~5,  ~5,  ~6,   0,   2,   2,   7,  ~1,  ~5,  ~7,  ~1,  ~3,   7,   6,   0,   2,   4,  ~5,   0,  ~4]]

fun f (x, y) = List.nth (List.nth (table, x), y)
fun show m = print (Matrix.toString (m, IntInf.toString))
structure Main =
   struct
      fun snf() =
         let val dim = 35
            val big = Matrix.map (Matrix.make (dim, dim, f), IntInf.fromInt)
            val entry = Matrix.fetch(smithNormalForm big, dim - 1, dim - 1)
(*          val _ = print (concat [IntInf.toString entry, "\n"]) *)
         in if entry = valOf (IntInf.fromString
                              "~1027954043102083189860753402541358641712697245")
               then ()
            else raise Fail "bug"
         end
      fun doit n =
         let
            val rec loop =
               fn 0 => ()
                | n => (snf(); loop(n - 1))
         in loop n
         end
   end

val foo = Main.doit 1;

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
