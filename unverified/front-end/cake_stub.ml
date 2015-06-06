module Cake_stub = struct
  type internal_type1 = int
  type int = internal_type1
  type internal_type2 = char
  type char = internal_type2
  type internal_type3 = string
  type string = internal_type3
  type internal_type4 = bytes
  type bytes = internal_type4
  type internal_type5 = exn
  type exn = internal_type5
  type 'a internal_type6 = 'a array
  type 'a array = 'a internal_type6

  let implode (l : char list) : string = 
    String.concat "" (List.map (String.make 1) l)

  let explode (s : string) : char list =
    let rec build i =
      if i = 0 then
        []
      else
        String.get s (i - 1) :: build (i - 1)
    in
    build (String.length s)
end
