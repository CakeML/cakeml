(* From the SML/NJ benchmark suite. *)

(* term.sml *)

structure Term =
struct
  datatype term
    = STR of string * term list
    | INT of int
    | CON of string
    | REF of term option ref

  exception BadArg of string
end;

(* trail.sml *)

structure Trail =
struct
  local
      open Term
      val global_trail = ref (nil : term option ref list)
      val trail_counter = ref 0
  in
      fun unwind_trail (0, tr) = tr
        | unwind_trail (n, r::tr) =
          ( r := NONE ; unwind_trail (n-1, tr) )
        | unwind_trail (_, nil) =
          raise BadArg "unwind_trail"

      fun reset_trail () = ( global_trail := nil )

      fun trail func =
          let
              val tc0 = !trail_counter
          in
              ( func () ;
               global_trail :=
                 unwind_trail (!trail_counter-tc0, !global_trail) ;
               trail_counter := tc0 )
          end

      fun bind (r, t) =
          ( r := SOME t ;
           global_trail := r::(!global_trail) ;
           trail_counter := !trail_counter+1 )
  end (* local *)
end; (* Trail *)

(* unify.sml *)

structure Unify =
struct
  local
    open Term Trail
    fun same_ref (r, REF(r')) = (r = r')
      | same_ref _ = false

    fun occurs_check r t =
        let
            fun oc (STR(_,ts)) = ocs ts
              | oc (REF(r')) =
                (case !r' of
                     SOME(s) => oc s
                   | _ => r <> r')
              | oc (CON _) = true
              | oc (INT _) = true
            and ocs nil = true
              | ocs (t::ts) = oc t andalso ocs ts
        in
            oc t
        end
    fun deref (t as (REF(x))) =
        (case !x of
             SOME(s) => deref s
           | _ => t)
      | deref t = t
    fun unify' (REF(r), t) sc = unify_REF (r,t) sc
      | unify' (s, REF(r)) sc = unify_REF (r,s) sc
      | unify' (STR(f,ts), STR(g,ss)) sc =
        if (f = g)
            then unifys (ts,ss) sc
        else ()
      | unify' (CON(f), CON(g)) sc =
        if (f = g) then
            sc ()
        else
            ()
      | unify' (INT(f), INT(g)) sc =
        if (f = g) then
            sc ()
        else
            ()
      | unify' (_, _) sc = ()
    and unifys (nil, nil) sc = sc ()
      | unifys (t::ts, s::ss) sc =
        unify' (deref(t), deref(s))
        (fn () => unifys (ts, ss) sc)
      | unifys _ sc = ()
    and unify_REF (r, t) sc =
        if same_ref (r, t)
            then sc ()
        else if occurs_check r t
                 then ( bind(r, t) ; sc () )
             else ()
  in
    val deref = deref
    fun unify (s, t) = unify' (deref(s), deref(t))
  end (* local *)
end; (* Unify *)

(* data.sml *)

structure Data =
struct
  local
    open Term Trail Unify
    val cons_s = "cons"
    val x_s = "x"
    val nil_s = "nil"
    val o_s = "o"
    val s_s = "s"
    val CON_o_s = CON(o_s)
    val CON_nil_s = CON(nil_s)
    val CON_x_s = CON(x_s)
  in
      fun exists sc = sc (REF(ref(NONE)))

fun move_horiz (T_1, T_2) sc =
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
(
trail (fn () =>
exists (fn T =>
exists (fn TT =>
unify (T_1, STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, T])])]), TT])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, T])])]), TT])) (fn () =>
sc ())))))
;
exists (fn P1 =>
exists (fn P5 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [P5, CON_nil_s])])])])]), TT])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [P5, CON_nil_s])])])])]), TT])) (fn () =>
sc ())))))
))
;
exists (fn P1 =>
exists (fn P2 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [P2, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, CON_nil_s])])])])]), TT])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [P2, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, CON_nil_s])])])])]), TT])) (fn () =>
sc ())))))
))
;
exists (fn L1 =>
exists (fn P4 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [P4, CON_nil_s])])])]), TT])])) (fn () =>
unify (T_2, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [P4, CON_nil_s])])])]), TT])])) (fn () =>
sc ())))))
))
;
exists (fn L1 =>
exists (fn P1 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, CON_nil_s])])])]), TT])])) (fn () =>
unify (T_2, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, CON_nil_s])])])]), TT])])) (fn () =>
sc ())))))
))
;
exists (fn L1 =>
exists (fn L2 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [L1, STR(cons_s, [L2, STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, CON_nil_s])])]), TT])])])) (fn () =>
unify (T_2, STR(cons_s, [L1, STR(cons_s, [L2, STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, CON_nil_s])])]), TT])])])) (fn () =>
sc ())))))
))
;
exists (fn T =>
exists (fn TT =>
unify (T_1, STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, T])])]), TT])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, T])])]), TT])) (fn () =>
sc ()))))
))
;
exists (fn P1 =>
exists (fn P5 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [P5, CON_nil_s])])])])]), TT])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [P5, CON_nil_s])])])])]), TT])) (fn () =>
sc ())))))
))
;
exists (fn P1 =>
exists (fn P2 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [P2, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])])])])]), TT])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [P2, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, CON_nil_s])])])])]), TT])) (fn () =>
sc ())))))
))
;
exists (fn L1 =>
exists (fn P4 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [P4, CON_nil_s])])])]), TT])])) (fn () =>
unify (T_2, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, STR(cons_s, [P4, CON_nil_s])])])]), TT])])) (fn () =>
sc ())))))
))
;
exists (fn L1 =>
exists (fn P1 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])])])]), TT])])) (fn () =>
unify (T_2, STR(cons_s, [L1, STR(cons_s, [STR(cons_s, [P1, STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, CON_nil_s])])])]), TT])])) (fn () =>
sc ())))))
))
;
exists (fn L1 =>
exists (fn L2 =>
exists (fn TT =>
unify (T_1, STR(cons_s, [L1, STR(cons_s, [L2, STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])])]), TT])])])) (fn () =>
unify (T_2, STR(cons_s, [L1, STR(cons_s, [L2, STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_o_s, CON_nil_s])])]), TT])])])) (fn () =>
sc ())))))
)
(*  | move_horiz _ _ = () *)

and rotate (T_1, T_2) sc =
exists (fn P11 =>
exists (fn P12 =>
exists (fn P13 =>
exists (fn P14 =>
exists (fn P15 =>
exists (fn P21 =>
exists (fn P22 =>
exists (fn P23 =>
exists (fn P24 =>
exists (fn P31 =>
exists (fn P32 =>
exists (fn P33 =>
exists (fn P41 =>
exists (fn P42 =>
exists (fn P51 =>
unify (T_1, STR(cons_s, [STR(cons_s, [P11, STR(cons_s, [P12, STR(cons_s, [P13, STR(cons_s, [P14, STR(cons_s, [P15, CON_nil_s])])])])]), STR(cons_s, [STR(cons_s, [P21, STR(cons_s, [P22, STR(cons_s, [P23, STR(cons_s, [P24, CON_nil_s])])])]), STR(cons_s, [STR(cons_s, [P31, STR(cons_s, [P32, STR(cons_s, [P33, CON_nil_s])])]), STR(cons_s, [STR(cons_s, [P41, STR(cons_s, [P42, CON_nil_s])]), STR(cons_s, [STR(cons_s, [P51, CON_nil_s]), CON_nil_s])])])])])) (fn () =>
unify (T_2, STR(cons_s, [STR(cons_s, [P51, STR(cons_s, [P41, STR(cons_s, [P31, STR(cons_s, [P21, STR(cons_s, [P11, CON_nil_s])])])])]), STR(cons_s, [STR(cons_s, [P42, STR(cons_s, [P32, STR(cons_s, [P22, STR(cons_s, [P12, CON_nil_s])])])]), STR(cons_s, [STR(cons_s, [P33, STR(cons_s, [P23, STR(cons_s, [P13, CON_nil_s])])]), STR(cons_s, [STR(cons_s, [P24, STR(cons_s, [P14, CON_nil_s])]), STR(cons_s, [STR(cons_s, [P15, CON_nil_s]), CON_nil_s])])])])])) (fn () =>
sc ())))))))))))))))))
(*  | rotate _ _ = () *)

and move (T_1, T_2) sc =
(
trail (fn () =>
(
trail (fn () =>
exists (fn X =>
exists (fn Y =>
unify (T_1, X) (fn () =>
unify (T_2, Y) (fn () =>
move_horiz (X, Y) sc)))))
;
exists (fn X =>
exists (fn X1 =>
exists (fn Y =>
exists (fn Y1 =>
unify (T_1, X) (fn () =>
unify (T_2, Y) (fn () =>
rotate (X, X1) (fn () =>
move_horiz (X1, Y1) (fn () =>
rotate (Y, Y1) sc))))))))
))
;
exists (fn X =>
exists (fn X1 =>
exists (fn Y =>
exists (fn Y1 =>
unify (T_1, X) (fn () =>
unify (T_2, Y) (fn () =>
rotate (X1, X) (fn () =>
move_horiz (X1, Y1) (fn () =>
rotate (Y1, Y) sc))))))))
)
(*  | move _ _ = () *)

and solitaire (T_1, T_2, T_3) sc =
(
trail (fn () =>
exists (fn X =>
unify (T_1, X) (fn () =>
unify (T_2, STR(cons_s, [X, CON_nil_s])) (fn () =>
unify (T_3, INT(0)) (fn () =>
sc ())))))
;
exists (fn N =>
exists (fn X =>
exists (fn Y =>
exists (fn Z =>
unify (T_1, X) (fn () =>
unify (T_2, STR(cons_s, [X, Z])) (fn () =>
unify (T_3, STR(s_s, [N])) (fn () =>
move (X, Y) (fn () =>
solitaire (Y, Z, N) sc))))))))
)
(*  | solitaire _ _ = () *)

and solution1 (T_1) sc =
exists (fn X =>
unify (T_1, X) (fn () =>
solitaire (STR(cons_s, [STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])])])])]), STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s,
 CON_nil_s])])])]), STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])])]), STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])]), STR(cons_s, [STR(cons_s, [CON_x_s, CON_nil_s]), CON_nil_s])])])])])
, X, STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [INT(0)])])])])])])])])])])])])])) sc))
(*  | solution1 _ _ = () *)

and solution2 (T_1) sc =
exists (fn X =>
unify (T_1, X) (fn () =>
solitaire (STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])])])])]), STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s,
 CON_nil_s])])])]), STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_o_s, STR(cons_s, [CON_x_s, CON_nil_s])])]), STR(cons_s, [STR(cons_s, [CON_x_s, STR(cons_s, [CON_x_s, CON_nil_s])]), STR(cons_s, [STR(cons_s, [CON_x_s, CON_nil_s]), CON_nil_s])])])])])
, X, STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [STR(s_s, [INT(0)])])])])])])])])])])])])])) sc))
(*  | solution2 _ _ = ()  *)
  end (* local *)
end; (* Data *)
signature BMARK =
  sig
    val doit : int -> unit
    val testit : TextIO.outstream -> unit
  end;
(* main.sml *)

structure Main : BMARK =
  struct
    val name = "Logic"

    exception Done

    fun testit strm = Data.exists(fn Z => Data.solution2 Z (fn () => raise Done))
          handle Done => TextIO.output(strm, "yes\n")

    fun doit () = Data.exists(fn Z => Data.solution2 Z (fn () => raise Done))
          handle Done => ()

    val doit =
       fn size =>
       let
          fun loop n =
             if n = 0
                then ()
             else (doit();
                   loop(n-1))
       in loop size
       end

  end; (* Main *)

val foo = Main.doit 50;

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
