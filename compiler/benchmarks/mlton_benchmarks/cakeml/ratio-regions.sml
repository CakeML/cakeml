(*
 * Translated from Jeff Siskind's Scheme code by Stephen Weeks
 * (sweeks@sweeks.com).
 * Here is the description from Jeff Siskind (qobi@research.nj.nec.com)
 *
 * It is an implementation of Ratio
 * Regions, an image segmentation/contour finding technique due to Ingemar Cox,
 * Satish Rao, and Yu Zhong. The algorithm is a reduction to max flow, an
 * unpublished technique that Satish described to me. Peter Blicher originally
 * implemented this via a translation to Andrew Goldberg's generic max-flow code.
 * I've reimplemented it, specializing the max-flow algorithm to the particular
 * graphs that are produced by Satish's reduction instead of using Andrew's code.
 * The max-flow algorithm is preflow-push with periodic relabeling and a
 * wave-based heuristic for scheduling pushes and lifts due to Sebastien Roy.
 *)
fun print _ = ()

exception Fail of string


fun doo(max: int, f: int -> unit) =
   let fun loop i = if i >= max then () else (f i; loop(i + 1))
   in loop 0
   end

fun zero x = x = 0
fun cons(x,y) =  x::y
fun make_vector (x,y) = Array.array x y
val vector_length = Array.length
fun vector_ref (x,y) = Array.sub x y
fun vector_set (x,y,z) = Array.update x y z
fun map_n_vector (x,y) = Array.tabulate x y
val string_length = String.size
fun string_ref (x,y) = String.sub x y
fun write_char c = () (* TextIO.output1(TextIO.stdOut, c) *)
fun modulo (x,y) = x mod y
fun quotient (x,y) = x div y
fun for_each(l, f) = List.app f l
fun negative x = x < 0
fun positive x = x > 0

fun imin (x,y) = min x y;

fun min l =
   case l of
      x :: l => let
                   fun loop(l, min) =
                      case l of
                         [] => min
                       | x :: l => loop(l, imin(min, x))
                in loop(l, x)
                end
    | _ => raise Fail "min"

fun every_n(n, p) =
   let fun loop i = i >= n orelse (p i andalso loop(i + 1))
   in loop 0
   end

fun some(l, p) = List.exists p l

fun some_n(n, p) =
   let fun loop i = i < n andalso (p i orelse loop(i + 1))
   in loop 0
   end

fun some_vector(v, p) =
   let
      fun loop i =
         i < vector_length v
         andalso (p(vector_ref(v, i))
                  orelse loop(i + 1))
   in loop 0
   end

fun x(x, _) = x
fun y(_, y) = y

datatype 'a matrix = Matrix ('a array array)

fun make_matrix(m: int, n: int, a) =
   Matrix(map_n_vector(m, fn i => make_vector(n, a)))

fun matrix_rows(Matrix a) = vector_length a
fun matrix_columns(Matrix a) = vector_length(vector_ref(a, 0))
fun matrix_ref(Matrix a, i, j) = vector_ref(vector_ref(a, i), j)
fun matrix_set(Matrix a, i, j, x) = vector_set(vector_ref(a, i), j, x)

datatype pormatValue = Int int | String string

fun pormat(control_string: string, values: pormatValue list) =
   let
      fun loop(i: int, values: pormatValue list) =
         if not(i = string_length control_string)
            then
               let val c = string_ref(control_string, i)
               in if c = #"~"
                     then let val c2 = string_ref(control_string, i + 1)
                          in case (c2, values) of
                             (#"s", Int n :: values) =>
                                (print(Int.toString n) ; loop(i + 2, values))
                           | (#"a", String s :: values) =>
                                (print s ; loop(i + 2, values))
                           | (#"%", _) =>
                                (print "\n"; loop(i + 2, values))
                           | _ => (write_char c; loop(i + 1, values))
                          end
                  else (write_char c ; loop(i + 1, values))
               end
         else ()
   in loop(0, values)
   end

(* The vertices are s, t, and (y,x).
 * C_RIGHT[y,x] is the capacity from (y,x) to (y,x+1) which is the same as the
 * capacity from (y,x+1) to (y,x).
 * C_DOWN[y,x] is the capacity from (y,x) to (y+1,x) which is the same as the
 * capacity from (y+1,x) to (y,x).
 * The capacity from s to (y,0), (0,x), (y,Y_1), (0,X_1) is implicitly
 * infinite.
 * The capacity from (x,y) to t is V*W[y,x].
 * F_RIGHT[y,x] is the preflow from (y,x) to (y,x+1) which is the negation of
 * the preflow from (y,x+1) to (y,x).
 * F_DOWN[y,x] is the preflow from (y,x) to (y+1,x) which is the negation of
 * the preflow from (y+1,x) to (y,x).
 * We do not record the preflow from s to (y,X_1), (y,0), (Y_1,x), and (0,x)
 * and from (y,X_1), (y,0), (Y_1,x), and (0,x) to s.
 * F_T[y,x] is the preflow from (y,x) to t.
 * We do not record the preflow from t to (y,x).
 * {C,F}_RIGHT[0:Y_1,0:X_2].
 * {C,F}_DOWN[0:Y_2,0:X_1].
 * F_T[0:Y_1,0:X_1]
 * For now, we will keep all capacities (and thus all preflows) as integers.
 * (CF_RIGHT y x) is the residual capacity from (y,x) to (y,x+1).
 * (CF_LEFT y x) is the residual capacity from (y,x) to (y,x_1).
 * (CF_DOWN y x) is the residual capacity from (y,x) to (y+1,x).
 * (CF_UP y x) is the residual capacity from (y,x) to (y_1,x).
 * We do not compute the residual capacities from s to (y,X_1), (y,0),
 * (Y_1,x), and (0,x) because they are all infinite.
 * We do not compute the residual capacities from (y,X_1), (y,0), (Y_1,x),
 * and (0,x) to s because they will never be used.
 * (CF_T y x) is the residual capacity from (y,x) to t.
 * We do not compute the residual capacity from t to (y,x) because it will
 * be used.
 * (EF_RIGHT? y x) is True if there is an edge from (y,x) to (y,x+1) in the
 * residual network.
 * (EF_LEFT? y x) is True if there is an edge from (y,x) to (y,x_1) in the
 * residual network.
 * (EF_DOWN? y x) is True if there is an edge from (y,x) to (y+1,x) in the
 * residual network.
 * (EF_UP? y x) is True if there is an edge from (y,x) to (y_1,x) in the
 * residual network.
 * (EF_T? y x) is True if there is an edge from (y,x) to t in the
 * residual network.
 * There are always edges in the residual network from s to (y,X_1), (y,0),
 * (Y_1,x), and (0,x).
 * We don't care whether there are edges in the residual network from
 * (y,X_1), (y,0), (Y_1,x), and (0,x) to s because they will never be used.
 * We don't care whether there are edges in the residual network from t to
 * (y,x) because they will never be used.
 *)

fun positive_min(x, y) = if negative x then y else imin(x, y)

fun positive_minus(x, y) = if negative x then x else x - y

fun positive_plus(x, y) = if negative x then x else x + y

datatype 'a queue =
   Nil
 | Cons 'a ('a queue ref)

fun rao_ratio_region(c_right, c_down, w, lg_max_v) =
   let val height = matrix_rows w
      val width  = matrix_columns w
      val f_right = make_matrix(height, width - 1, 0)
      val f_down = make_matrix(height - 1, width, 0)
      val f_t = make_matrix(height, width, 0)
      val h = make_matrix(height, width, 0)
      val e = make_matrix(height, width, 0)
      val marked = make_matrix(height, width, False)
      val m1 = height * width + 2
      val m2 = 2 * height * width + 2
      val q = make_vector(2 * height * width + 3, [])
      fun cf_right(y, x) =
         matrix_ref(c_right, y, x) - matrix_ref(f_right, y, x)
      fun cf_left(y, x) =
         matrix_ref(c_right, y, x - 1) + matrix_ref(f_right, y, x - 1)
      fun cf_down(y, x) =
         matrix_ref(c_down, y, x) - matrix_ref(f_down, y, x)
      fun cf_up(y, x) =
         matrix_ref(c_down, y - 1, x) + matrix_ref(f_down, y - 1, x)
      fun ef_right(y, x) = positive(cf_right(y, x))
      fun ef_left(y, x) = positive(cf_left(y, x))
      fun ef_down(y, x) = positive(cf_down(y, x))
      fun ef_up(y, x) = positive(cf_up(y, x))
      fun preflow_push v =
         let
            fun enqueue(y, x) =
               if not(matrix_ref(marked, y, x))
                  then
                     (vector_set(q,
                                 matrix_ref(h, y, x),
                                 (cons((x, y),
                                       vector_ref(q, matrix_ref(h, y, x)))))
                      ; matrix_set(marked, y, x, True))
               else ()
            fun cf_t(y, x) = v * matrix_ref(w, y, x) - matrix_ref(f_t, y, x)
            fun ef_t(y, x) = positive(cf_t(y, x))
            fun can_push_right(y, x) =
               x < width - 1
               andalso not(zero(matrix_ref(e, y, x)))
               andalso ef_right(y, x)
               andalso matrix_ref(h, y, x) = matrix_ref(h, y, x + 1) + 1
            fun can_push_left(y, x) =
               x > 0
               andalso not(zero(matrix_ref(e, y, x)))
               andalso ef_left(y, x)
               andalso matrix_ref(h, y, x) = matrix_ref(h, y, x - 1) + 1
            fun can_push_down(y, x) =
               y < height - 1
               andalso not(zero(matrix_ref(e, y, x)))
               andalso ef_down(y, x)
               andalso matrix_ref(h, y, x) = matrix_ref(h, y + 1, x) + 1
            fun can_push_up(y, x) =
               y > 0
               andalso not(zero(matrix_ref(e, y, x)))
               andalso ef_up(y, x)
               andalso matrix_ref(h, y, x) = matrix_ref(h, y - 1, x) + 1
            fun can_push_t(y, x) =
               not(zero(matrix_ref(e, y, x)))
               andalso ef_t(y, x)
               andalso matrix_ref(h, y, x) = 1
            fun can_lift(y, x) =
               not(zero(matrix_ref(e, y, x)))
               andalso (if x = width - 1
                           then matrix_ref(h, y, x) <= m1
                        else (not(ef_right(y, x))
                              orelse
                              matrix_ref(h, y, x) <= matrix_ref(h, y, x + 1)))
               andalso (if x = 0
                           then matrix_ref(h, y, x) <= m1
                        else (not(ef_left(y, x))
                              orelse
                              matrix_ref(h, y, x) <= matrix_ref(h, y, x - 1)))
               andalso (if y = height - 1
                           then matrix_ref(h, y, x) <= m1
                        else (not(ef_down(y, x))
                              orelse
                              matrix_ref(h, y, x) <= matrix_ref(h, y + 1, x)))
               andalso (if y = 0
                           then matrix_ref(h, y, x) <= m1
                        else (not(ef_up(y, x))
                              orelse
                              matrix_ref(h, y, x) <= matrix_ref(h, y - 1, x)))
               andalso (not(ef_t(y, x)) orelse matrix_ref(h, y, x) = 0)
            fun push_right(y, x) =
               (* (pormat "Push right ~s ~s~%" y x) *)
               let val df_u_v = positive_min(matrix_ref(e, y, x), cf_right(y, x))
               in matrix_set(f_right, y, x, matrix_ref(f_right, y, x) + df_u_v)
                  ; matrix_set(e, y, x,
                               positive_minus(matrix_ref(e, y, x), df_u_v))
                  ; matrix_set(e, y, x + 1,
                               positive_plus(matrix_ref(e, y, x + 1), df_u_v))
                  ; enqueue(y, x + 1)
               end
            fun push_left(y, x) =
               (* (pormat "Push left ~s ~s~%" y x) *)
               let val df_u_v = positive_min(matrix_ref(e, y, x), cf_left(y, x))
               in matrix_set(f_right, y, x - 1,
                             matrix_ref(f_right, y, x - 1) - df_u_v)
                  ; matrix_set(e, y, x,
                               positive_minus(matrix_ref(e, y, x), df_u_v))
                  ; matrix_set(e, y, x - 1,
                               positive_plus(matrix_ref(e, y, x - 1), df_u_v))
                  ; enqueue(y, x - 1)
               end
            fun push_down(y, x) =
               (* (pormat "Push down ~s ~s~%" y x) *)
               let val df_u_v = positive_min(matrix_ref(e, y, x), cf_down(y, x))
               in matrix_set(f_down, y, x, matrix_ref(f_down, y, x) + df_u_v)
                  ; matrix_set(e, y, x,
                               positive_minus(matrix_ref(e, y, x), df_u_v))
                  ; matrix_set(e, y + 1, x,
                               positive_plus(matrix_ref(e, y + 1, x), df_u_v))
                  ; enqueue(y + 1, x)
               end
            fun push_up(y, x) =
               (* ;;(pormat "Push up ~s ~s~%" y x) *)
               let val df_u_v = positive_min(matrix_ref(e, y, x), cf_up(y, x))
               in matrix_set(f_down, y - 1, x,
                             matrix_ref(f_down, y - 1, x) - df_u_v)
                  ; matrix_set(e, y, x,
                               positive_minus(matrix_ref(e, y, x), df_u_v))
                  ; matrix_set(e, y - 1, x,
                               positive_plus(matrix_ref(e, y - 1, x), df_u_v))
                  ; enqueue(y - 1, x)
               end
            fun push_t(y, x) =
               (* ;;(pormat "Push t ~s ~s~%" y x) *)
               let val df_u_v = positive_min(matrix_ref(e, y, x), cf_t(y, x))
               in matrix_set(f_t, y, x, matrix_ref(f_t, y, x) + df_u_v)
                  ; matrix_set(e, y, x,
                               positive_minus(matrix_ref(e, y, x), df_u_v))
               end
            fun lift(y, x) =
               (* ;;(pormat "Lift ~s ~s~%" y x) *)
               matrix_set
               (h, y, x,
                1 + min[if x = width - 1
                           then m1
                        else if ef_right(y, x)
                                then matrix_ref(h, y, x + 1)
                             else m2,
                        if x = 0
                           then m1
                        else if ef_left(y, x)
                                then matrix_ref(h, y, x - 1)
                             else m2,
                        if y = height - 1
                           then m1
                        else if ef_down(y, x)
                                then matrix_ref(h, y + 1, x)
                             else m2,
                        if y = 0
                           then m1
                        else if ef_up(y, x)
                                then matrix_ref(h, y - 1, x)
                             else m2,
                        if ef_t(y, x) then 0 else m2])
            fun relabel() =
               (* ;;(pormat "Relabel~%") *)
               let
                  fun null(q) =
                     case !q of
                        Nil => True
                      | _ => False
                  val q= Ref Nil : (int * int) queue ref
                  val tail = Ref Nil : (int * int) queue ref
                  fun enqueue(y, x, value) =
                     if value < matrix_ref(h, y, x)
                        then (matrix_set(h, y, x, value)
                              ; if not(matrix_ref(marked, y, x))
                                   then (matrix_set(marked, y, x, True)
                                         ; (case !tail of
                                               Nil =>
                                                  (tail := Cons (x, y) (Ref Nil)
                                                   ; q := !tail)
                                             | Cons _ cdr =>
                                                  (cdr := Cons (x, y) (Ref Nil)
                                                   ; tail := !cdr)))
                                else ())
                     else ()
                  fun dequeue() =
                     case !q of
                        Nil => raise Fail "dequeue"
                      | Cons p rest =>
                         (matrix_set(marked, y p, x p, False)
                          ; q := !rest
                          ; if null q then tail := Nil else ()
                          ; p)
               in doo(height, fn y =>
                     doo(width, fn x =>
                        (matrix_set(h, y, x, m1)
                         ; matrix_set(marked, y, x, False))))
                  ; doo(height, fn y =>
                       doo(width, fn x =>
                          if ef_t(y, x)
                             andalso matrix_ref(h, y, x) > 1
                             then enqueue(y, x, 1)
                          else ()))
                  ; let
                       fun loop() =
                          if not(null q)
                             then
                                (let val p = dequeue()
                                     val x = x p
                                     val y = y p
                                     val value = matrix_ref(h, y, x) + 1
                                 in if x > 0 andalso ef_right(y, x - 1)
                                       then enqueue(y, x - 1, value)
                                    else ()
                                    ; if x < width - 1 andalso ef_left(y, x + 1)
                                         then enqueue(y, x + 1, value)
                                      else ()
                                    ; if y > 0 andalso ef_down(y - 1, x)
                                         then enqueue(y - 1, x, value)
                                      else ()
                                    ; if y < height - 1 andalso ef_up(y + 1, x)
                                         then enqueue(y + 1, x, value)
                                      else ()
                                 end
                                 ; loop())
                          else ()
                    in loop()
                    end
               end (* relabel *)
         in doo(height, fn y =>
               doo(width, fn x =>
                  (matrix_set(e, y, x, 0)
                   ; matrix_set(f_t, y, x, 0))))
            ; doo(height, fn y =>
                 doo(width - 1, fn x =>
                    matrix_set(f_right, y, x, 0)))
            ; doo(height - 1, fn y =>
                 doo(width, fn x =>
                    matrix_set(f_down, y, x, 0)))
            ; doo(height, fn y =>
                 (matrix_set(e, y, width - 1, ~1)
                  ; matrix_set(e, y, 0, ~1)))
            ; doo(width - 1, fn x =>
                 (matrix_set(e, height - 1, x, ~1)
                  ; matrix_set(e, 0, x, ~1)))
            ; let val pushes = Ref 0
                  val lifts = Ref 0
                  val relabels = Ref 0
                  fun loop(i, p) =
                     if zero(modulo(i, 6)) andalso not p
                        then (relabel()
                              ; relabels := !relabels + 1
                              ; if every_n(height, fn y =>
                                           every_n(width, fn x =>
                                                   zero(matrix_ref(e, y, x))
                                                   orelse
                                                   matrix_ref(h, y, x) = m1))
                                   then
                                      (* Every vertex with excess capacity is not reachable from the sink in
                                       * the inverse residual network. So terminate early because we have
                                       * already found a min cut. In this case, the preflows and excess
                                       * capacities will not be correct. But the cut is indicated by the
                                       * heights. Vertices reachable from the source have height
                                       * HEIGHT * WIDTH + 2 while vertices reachable from the sink have
                                       * smaller height. Early termination is necessary with relabeling to
                                       * prevent an infinite loop. The loop arises because vertices that are
                                       * not reachable from the sink in the inverse residual network have
                                       * their height reset to HEIGHT * WIDTH + 2 by the relabeling
                                       * process. If there are such vertices with excess capacity, this is
                                       * not high enough for the excess capacity to be pushed back to the
                                       * perimeter. So after relabeling, vertices get lifted to try to push
                                      * excess capacity back to the perimeter but then a relabeling happens
                                      * to soon and foils this lifting. Terminating when all vertices with
                                      * excess capacity are not reachable from the sink in the inverse
                                      * residual network eliminates this problem.
                                      *)
                                      (pormat
                                       ("~s push~a, ~s lift~a, ~s relabel~a, ~s wave~a, terminated early~%",
                                        [Int(! pushes),
                                         String(if !pushes = 1 then "" else "es"),
                                         Int(! lifts),
                                         String(if !lifts = 1 then "" else "s"),
                                         Int(! relabels),
                                         String(if !relabels = 1 then "" else "s"),
                                         Int i,
                                         String(if i = 1 then "" else "s")]))
                                else
                                   (* We need to rebuild the priority queue after relabeling since the
                                    * heights might have changed and the priority queue is indexed by
                                    * height. This also assumes that a relabel is done before any pushes
                                    * or lifts.
                                    *)
                                   (doo(vector_length q, fn k =>
                                       vector_set(q, k, []))
                                    ; doo(height, fn y =>
                                         doo(width, fn x =>
                                            matrix_set(marked, y, x, False)))
                                    ; doo(height, fn y =>
                                         doo(width, fn x =>
                                            if not(zero(matrix_ref(e, y, x)))
                                               then enqueue(y, x)
                                            else ()))
                                    ; loop(i, True)))
                     else if some_vector(q, fn ps =>
                                         some(ps, fn p =>
                                              let val x = x p
                                                 val y = y p
                                              in can_push_right(y, x)
                                                 orelse can_push_left(y, x)
                                                 orelse can_push_down(y, x)
                                                 orelse can_push_up(y, x)
                                                 orelse can_push_t(y, x)
                                                 orelse can_lift(y, x)
                                              end))
                             then
                                (
                                 let fun loop k =
                                    if not(negative k)
                                       then
                                          (
                                           let val ps = vector_ref(q, k)
                                           in vector_set(q, k, [])
                                              ; (for_each
                                                 (ps, fn p =>
                                                  matrix_set(marked, y p, x p,
                                                             False)))
                                              ; (for_each
                                                 (ps, fn p =>
                                                  let val x = x p
                                                     val y = y p
                                                  in if can_push_right(y, x)
                                                        then (pushes := !pushes + 1
                                                              ; push_right(y, x))
                                                     else ()
                                                        ; if can_push_left(y, x)
                                                             then (pushes := !pushes + 1
                                                                   ; push_left(y, x))
                                                          else ()
                                                             ; if can_push_down(y, x)
                                                                  then (pushes := !pushes + 1
                                                                        ; push_down(y, x))
                                                               else ()
                                                                  ; if can_push_up(y, x)
                                                                       then (pushes := !pushes + 1
                                                                             ; push_up(y, x))
                                                                    else ()
                                                                       ; if can_push_t(y, x)
                                                                            then (pushes := !pushes + 1
                                                                                  ; push_t(y, x))
                                                                         else ()
                                                                            ; if can_lift(y, x)
                                                                                 then (lifts := !lifts + 1
                                                                                       ; lift(y, x))
                                                                              else ()
                                                                                 ; if not(zero(matrix_ref(e, y, x)))
                                                                                      then enqueue(y, x)
                                                                                   else ()
                                                  end))
                                           end
                                        ; loop(k - 1))
                                    else ()
                                 in loop(vector_length q - 1)
                                 end
                              ; loop(i + 1, False))
                          else
                             (* This is so MIN_CUT and MIN_CUT_INCLUDES_EVERY_EDGE_TO_T work. *)
                             (relabel()
                              ; relabels := !relabels + 1
                              ; (pormat("~s push~a, ~s lift~a, ~s relabel~a, ~s wave~a~%",
                                          [Int(! pushes),
                                           String(if !pushes = 1 then "" else "es"),
                                           Int(! lifts),
                                           String(if !lifts = 1 then "" else "s"),
                                           Int(! relabels),
                                           String(if !relabels = 1 then "" else "s"),
                                           Int i,
                                           String(if i = 1 then "" else "s")])))
              in loop(0, False)
              end
         end
           fun min_cut_includes_every_edge_to_t() =
              (* This requires that a relabel was done immediately before returning from
               * PREFLOW_PUSH.
               *)
             every_n(height, fn y =>
                     every_n(width, fn x =>
                             matrix_ref(h, y, x) = m1))
           fun min_cut() =
              (* This requires that a relabel was done immediately before returning from
               * PREFLOW_PUSH
               *)
              map_n_vector
              (height, fn y =>
               map_n_vector(width, fn x =>
                            not(matrix_ref(h, y, x) = m1)))

           fun loop(lg_v, v_max) =
              if negative lg_v
                 then (pormat("V-MAX=~s~%",[Int v_max])
                       ; preflow_push(v_max + 1)
                       ; min_cut())
              else let val v = v_max + let
                                          fun loop(i, c) =
                                             if (zero i)
                                                then c
                                             else loop(i - 1, c + c)
                                       in loop(lg_v, 1)
                                       end
                   in pormat("LG-V=~s, V-MAX=~s, V=~s~%",
                             [Int lg_v, Int v_max, Int v])
                      ; preflow_push v
                      ; loop(lg_v - 1,
                             if min_cut_includes_every_edge_to_t()
                                then v
                             else v_max)
                   end

   in  loop(lg_max_v, 0)
   end

fun doit n =
   let val height = n
      val width = n
      val lg_max_v = 15
      val c_right = make_matrix(height, width - 1, ~1)
      val c_down = make_matrix(height - 1, width, ~1)
   in doo(height, fn y =>
          doo(width - 1, fn x =>
              matrix_set
              (c_right, y, x,
               if (y >= quotient(height, 4)
                   andalso y < quotient(3 * height, 4)
                   andalso (x = quotient(width, 4) - 1
                            orelse x = quotient(3 * width, 4) - 1))
                  then 1
               else 128)))
      ; doo(height - 1, fn y =>
            doo(width, fn x =>
                matrix_set
                (c_down, y, x,
                 if (x >= quotient(width, 4)
                     andalso x < quotient(3 * width, 4)
                     andalso (y = quotient(height, 4) - 1
                              orelse y = quotient(3 * height, 4) - 1))
                    then 1
                 else 128)))
      ; rao_ratio_region(c_right, c_down,
                         make_matrix(height, width, 1),
                         lg_max_v)
   end

structure Main =
   struct
      val doit = doit
   end

val foo = Main.doit 250;
