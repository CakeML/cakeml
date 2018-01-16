fun main ()=
  let
  fun insert1 a n l =
    if n < l then
      (Array.update (a,n,1);
      insert1 a (n + 1) l)
    else
      ();

  fun lookup1 a n l =
    if n < l then
      (Array.sub (a,n);
      lookup1 a (n + 1) l)
    else
      ();

  fun ins_look a n =
    if n = 0 then
      ()
    else
      (insert1 a 0 (Array.length a); lookup1 a 0 (Array.length a); ins_look a (n - 1));

  fun harness n =
  let val a = Array.array (n,0) in
    ins_look a 500000
  end;

  val test = harness 1000;
in () end;
