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
  val global_trail = ref (nil : Term.term option ref list)
  val trail_counter = ref 0
  fun unwind_trail ps =
  case ps of
    (0, tr) => tr
  | (n, r::tr) => ( r := NONE ; unwind_trail (n-1, tr) )
  | (_, []) => raise Term.BadArg "unwind_trail"

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

end; (* Trail *)

(* unify.sml *)

structure Unify =
struct
  fun same_ref p =
    case p of
      (r, Term.REF(r')) => (r = r')
    | _ => false

  fun occurs_check r t =
      let
          fun oc p = case p of
            (Term.STR _ ts) => ocs ts
          | (Term.REF(r')) =>
              (case !r' of
                   SOME(s) => oc s
                 | _ => r <> r')
          | (Term.CON _) => true
          | (Term.INT _) => true
          and ocs ls = case ls of
            [] => true
          | (t::ts) => oc t andalso ocs ts
      in
          oc t
      end

  fun deref t =
    case t of
      (Term.REF(x)) =>
       (case !x of
            SOME(s) => deref s
          | _ => t)
     | t => t

  fun unify' p sc = case p of
    (Term.REF(r), t) => unify_REF (r,t) sc
  | (s, Term.REF(r)) => unify_REF (r,s) sc
  | (Term.STR f ts, Term.STR g ss) =>
       if (f = g)
           then unifys (ts,ss) sc
       else ()
  | (Term.CON(f), Term.CON(g)) =>
       if (f = g) then
           sc ()
       else
           ()
  | (Term.INT(f), Term.INT(g)) =>
    if (f = g) then
        sc ()
    else
        ()
  | _ => ()

  and unifys p sc = case p of
    ([], []) => sc ()
  | (t::ts, s::ss) =>
      unify' (deref(t), deref(s))
      (fn () => unifys (ts, ss) sc)
  | _ => ()
  and unify_REF p sc = case p of
    (r,t) =>
      if same_ref (r, t)
          then sc ()
      else if occurs_check r t
               then ( Trail.bind(r, t) ; sc () )
           else ()
  val deref = deref
  fun unify (s, t) = unify' (deref(s), deref(t))

end; (* Unify *)

structure Data =
struct
    val cons_s = "cons"
    val x_s = "x"
    val nil_s = "nil"
    val o_s = "o"
    val s_s = "s"
    val cON_o_s = Term.CON o_s
    val cON_nil_s = Term.CON(nil_s)
    val cON_x_s = Term.CON(x_s)

    fun exists sc = sc (Term.REF(ref(NONE)))

fun move_horiz (t_1, t_2) sc =
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
exists (fn t =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, t])])]), tt])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, t])])]), tt])) (fn () =>
sc ())))))
;
exists (fn p1 =>
exists (fn p5 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [p5, cON_nil_s])])])])]), tt])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [p5, cON_nil_s])])])])]), tt])) (fn () =>
sc ())))))
))
;
exists (fn p1 =>
exists (fn p2 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [p2, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, cON_nil_s])])])])]), tt])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [p2, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])])])]), tt])) (fn () =>
sc ())))))
))
;
exists (fn l1 =>
exists (fn p4 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [p4, cON_nil_s])])])]), tt])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [p4, cON_nil_s])])])]), tt])])) (fn () =>
sc ())))))
))
;
exists (fn l1 =>
exists (fn p1 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, cON_nil_s])])])]), tt])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])])]), tt])])) (fn () =>
sc ())))))
))
;
exists (fn l1 =>
exists (fn l2 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [l1, Term.STR cons_s ( [l2, Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, cON_nil_s])])]), tt])])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [l1, Term.STR cons_s ( [l2, Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])]), tt])])])) (fn () =>
sc ())))))
))
;
exists (fn t =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, t])])]), tt])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, t])])]), tt])) (fn () =>
sc ()))))
))
;
exists (fn p1 =>
exists (fn p5 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [p5, cON_nil_s])])])])]), tt])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [p5, cON_nil_s])])])])]), tt])) (fn () =>
sc ())))))
))
;
exists (fn p1 =>
exists (fn p2 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [p2, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])])])]), tt])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [p2, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, cON_nil_s])])])])]), tt])) (fn () =>
sc ())))))
))
;
exists (fn l1 =>
exists (fn p4 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [p4, cON_nil_s])])])]), tt])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [p4, cON_nil_s])])])]), tt])])) (fn () =>
sc ())))))
))
;
exists (fn l1 =>
exists (fn p1 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])])]), tt])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [l1, Term.STR cons_s ( [Term.STR cons_s ( [p1, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, cON_nil_s])])])]), tt])])) (fn () =>
sc ())))))
))
;
exists (fn l1 =>
exists (fn l2 =>
exists (fn tt =>
Unify.unify (t_1, Term.STR cons_s ( [l1, Term.STR cons_s ( [l2, Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])]), tt])])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [l1, Term.STR cons_s ( [l2, Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_o_s, cON_nil_s])])]), tt])])])) (fn () =>
sc ())))))
)
(*  | move_horiz _ _ = () *)

and rotate (t_1, t_2) sc =
exists (fn p11 =>
exists (fn p12 =>
exists (fn p13 =>
exists (fn p14 =>
exists (fn p15 =>
exists (fn p21 =>
exists (fn p22 =>
exists (fn p23 =>
exists (fn p24 =>
exists (fn p31 =>
exists (fn p32 =>
exists (fn p33 =>
exists (fn p41 =>
exists (fn p42 =>
exists (fn p51 =>
Unify.unify (t_1, Term.STR cons_s ( [Term.STR cons_s ( [p11, Term.STR cons_s ( [p12, Term.STR cons_s ( [p13, Term.STR cons_s ( [p14, Term.STR cons_s ( [p15, cON_nil_s])])])])]), Term.STR cons_s ( [Term.STR cons_s ( [p21, Term.STR cons_s ( [p22, Term.STR cons_s ( [p23, Term.STR cons_s ( [p24, cON_nil_s])])])]), Term.STR cons_s ( [Term.STR cons_s ( [p31, Term.STR cons_s ( [p32, Term.STR cons_s ( [p33, cON_nil_s])])]), Term.STR cons_s ( [Term.STR cons_s ( [p41, Term.STR cons_s ( [p42, cON_nil_s])]), Term.STR cons_s ( [Term.STR cons_s ( [p51, cON_nil_s]), cON_nil_s])])])])])) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [Term.STR cons_s ( [p51, Term.STR cons_s ( [p41, Term.STR cons_s ( [p31, Term.STR cons_s ( [p21, Term.STR cons_s ( [p11, cON_nil_s])])])])]), Term.STR cons_s ( [Term.STR cons_s ( [p42, Term.STR cons_s ( [p32, Term.STR cons_s ( [p22, Term.STR cons_s ( [p12, cON_nil_s])])])]), Term.STR cons_s ( [Term.STR cons_s ( [p33, Term.STR cons_s ( [p23, Term.STR cons_s ( [p13, cON_nil_s])])]), Term.STR cons_s ( [Term.STR cons_s ( [p24, Term.STR cons_s ( [p14, cON_nil_s])]), Term.STR cons_s ( [Term.STR cons_s ( [p15, cON_nil_s]), cON_nil_s])])])])])) (fn () =>
sc ())))))))))))))))))
(*  | rotate _ _ = () *)

and move (t_1, t_2) sc =
(
Trail.trail (fn () =>
(
Trail.trail (fn () =>
exists (fn x =>
exists (fn y =>
Unify.unify (t_1, x) (fn () =>
Unify.unify (t_2, y) (fn () =>
move_horiz (x, y) sc)))))
;
exists (fn x =>
exists (fn x1 =>
exists (fn y =>
exists (fn y1 =>
Unify.unify (t_1, x) (fn () =>
Unify.unify (t_2, y) (fn () =>
rotate (x, x1) (fn () =>
move_horiz (x1, y1) (fn () =>
rotate (y, y1) sc))))))))
))
;
exists (fn x =>
exists (fn x1 =>
exists (fn y =>
exists (fn y1 =>
Unify.unify (t_1, x) (fn () =>
Unify.unify (t_2, y) (fn () =>
rotate (x1, x) (fn () =>
move_horiz (x1, y1) (fn () =>
rotate (y1, y) sc))))))))
)
(*  | move _ _ = () *)

and solitaire (t_1, t_2, t_3) sc =
(
Trail.trail (fn () =>
exists (fn x =>
Unify.unify (t_1, x) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [x, cON_nil_s])) (fn () =>
Unify.unify (t_3, Term.INT(0)) (fn () =>
sc ())))))
;
exists (fn n =>
exists (fn x =>
exists (fn y =>
exists (fn z =>
Unify.unify (t_1, x) (fn () =>
Unify.unify (t_2, Term.STR cons_s ( [x, z])) (fn () =>
Unify.unify (t_3, Term.STR s_s ( [n])) (fn () =>
move (x, y) (fn () =>
solitaire (y, z, n) sc))))))))
)
(*  | solitaire _ _ = () *)

and solution1 (t_1) sc =
exists (fn x =>
Unify.unify (t_1, x) (fn () =>
solitaire (Term.STR cons_s ( [Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])])])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s,
 cON_nil_s])])])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, cON_nil_s]), cON_nil_s])])])])])
, x, Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.INT(0)])])])])])])])])])])])])])) sc))
(*  | solution1 _ _ = () *)

and solution2 (t_1) sc =
exists (fn x =>
Unify.unify (t_1, x) (fn () =>
solitaire (Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])])])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s,
 cON_nil_s])])])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_o_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, Term.STR cons_s ( [cON_x_s, cON_nil_s])]), Term.STR cons_s ( [Term.STR cons_s ( [cON_x_s, cON_nil_s]), cON_nil_s])])])])])
, x, Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.STR s_s ( [Term.INT(0)])])])])])])])])])])])])])) sc))
(*  | solution2 _ _ = ()  *)

end; (* Data *)

structure Main =
  struct
    val name = "Logic"

    exception Done

    fun testit () = Data.exists(fn z => Data.solution2 z (fn () => raise Done))
          handle Done => print "yes\n"

    fun doit () = Data.exists(fn z => Data.solution2 z (fn () => raise Done))
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
