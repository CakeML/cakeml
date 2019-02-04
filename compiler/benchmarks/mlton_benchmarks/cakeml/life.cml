structure Main =
  struct
    fun append x y = x @ y
    fun map f ls = case ls of
        [] => []
      | (a::x) => f a :: map f x

    exception Ex_undefined string
    fun error str = raise Ex_undefined str

    fun accumulate f = let
          fun foldf a ls = case ls of
              [] => a
            | (b::x) => foldf (f a b) x
          in
            foldf
          end

    fun filter p = let
          fun consifp x a = if p a then a::x else x
          in
            fn x => (List.rev (accumulate consifp [] x))
          end


    fun exists p = let fun existsp ls = case ls of
                       [] => False
                     | (a::x) => if p a then True else existsp x
                in existsp end

    fun equal a b = (a  = b)

    fun member x a = exists (equal a) x

    fun c f x y = f y x

    fun cons a x = a::x

    fun revonto x = accumulate (c cons) x

    fun length x = let fun count n a = n+1 in accumulate count 0 x end

    fun repeat f = let fun rptf n x = if n=0 then x else rptf(n-1)(f x)
                       fun check n = if n<0 then error "repeat<0" else n
                    in fn x => rptf (check x) end

    fun copy n x = repeat (cons x) n []

    fun spaces n = String.concat (copy n " ")

    fun lexordset ls = case ls of
      [] => []
    | (a::x) => append (lexordset (filter (lexless a) x))
                (append [a] (lexordset (filter (lexgreater a) x)))
    and lexless(a1:int,b1:int)(a2,b2) =
         if a2<a1 then True else if a2=a1 then b2<b1 else False
    and lexgreater pr1 pr2 = lexless pr2 pr1
    fun collect f list =
           let fun accumf sofar ls = case ls of
                   [] => sofar
                 | (a::x) => accumf (revonto sofar (f a)) x
            in accumf [] list
           end
    fun occurs3 x =
        (* finds coords which occur exactly 3 times in coordlist x *)
        let fun f xover x3 x2 x1 ls = case ls of
                [] => diff x3 xover
              | (a::x) =>
                 if member xover a then f xover x3 x2 x1 x else
                 if member x3 a then f (a::xover) x3 x2 x1 x else
                 if member x2 a then f xover (a::x3) x2 x1 x else
                 if member x1 a then f xover x3 (a::x2) x1 x else
                                     f xover x3 x2 (a::x1) x
            and diff x y = filter (fn x => not (member y x)) x
         in f [] [] [] [] x end

    datatype generation = GEN ((int*int) list)
    fun alive (GEN livecoords) = livecoords
    and mkgen coordlist = GEN (lexordset coordlist)
    and mk_nextgen_fn neighbours gen =
        let val living = alive gen
            val isalive = member living
            val liveneighbours = fn x => length (filter isalive (neighbours x))
            fun twoorthree n = n=2 orelse n=3
            val survivors = filter (fn x => twoorthree (liveneighbours x)) living
            val newnbrlist = collect (fn x => filter (fn y => not (isalive y)) (neighbours x)) living
            val newborn = occurs3 newnbrlist
         in mkgen (append survivors newborn) end

    fun neighbours (i,j) = [(i-1,j-1),(i-1,j),(i-1,j+1),
                            (i,j-1),(i,j+1),
                            (i+1,j-1),(i+1,j),(i+1,j+1)]


    val xstart = 0
    val ystart = 0
    fun markafter n string = String.concat [string ,spaces n,"0"]
    fun plotfrom (x,y) (* current position *)
                 str   (* current line being prepared -- a string *)
                 ls = case ls of
       ((x1,y1)::more)  (* coordinates to be plotted *)
        => if x=x1
           then (* same line so extend str and continue from y1+1 *)
                plotfrom(x,y1+1)(markafter(y1-y)str)more
           else (* flush current line and start a new line *)
                str :: plotfrom(x+1,ystart)""((x1,y1)::more)
      | [] => [str]
    fun good (x,y) = x>=xstart andalso y>=ystart
    fun plot coordlist = plotfrom(xstart,ystart) "" (filter good coordlist)

    fun at coordlist (x:int,y:int) = let fun move(a,b) = (a+x,b+y)
                                      in map move coordlist end
    val rotate = map (fn (x:int,y:int) => (y,~x))

    val glider = [(0,0),(0,2),(1,1),(1,2),(2,1)]
    val bail = [(0,0),(0,1),(1,0),(1,1)]
    fun barberpole n =
       let fun f i = if i=n then (n+n-1,n+n)::(n+n,n+n)::[]
                       else (i+i,i+i+1)::(i+i+2,i+i+1)::f(i+1)
        in (0,0)::(1,0):: f 0
       end

    val genB = mkgen(append (at glider (2,2)) (append (at bail (2,12))
                     (at (rotate (barberpole 4)) (5,20))))

    fun nthgen g i = case i of 0 => g | _ => nthgen (mk_nextgen_fn neighbours g) (i-1)

    val gun = mkgen
     [(2,20),(3,19),(3,21),(4,18),(4,22),(4,23),(4,32),(5,7),(5,8),(5,18),
      (5,22),(5,23),(5,29),(5,30),(5,31),(5,32),(5,36),(6,7),(6,8),(6,18),
      (6,22),(6,23),(6,28),(6,29),(6,30),(6,31),(6,36),(7,19),(7,21),(7,28),
      (7,31),(7,40),(7,41),(8,20),(8,28),(8,29),(8,30),(8,31),(8,40),(8,41),
      (9,29),(9,30),(9,31),(9,32)]

    fun show pr = fn x => (List.app (fn s => (pr s; pr "\n"))) (plot (alive x))

    fun doit () = show (fn _ => ()) (nthgen gun 25000)

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

    fun testit () = show (fn c => print  c) (nthgen gun 25000)

  end (* Life *)

val foo = Main.doit 2;
