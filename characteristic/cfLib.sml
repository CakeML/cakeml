(*
  This library collects all CF-related libraries and theories
  into a single import for convenience.
*)
structure cfLib = struct
  open
    cfHeapsBaseTheory cfHeapsTheory
    cfTacticsBaseLib cfTacticsLib
    cfLetAutoTheory cfLetAutoLib
    cfNormaliseLib
    cfMainTheory
    cfDivLib
end
