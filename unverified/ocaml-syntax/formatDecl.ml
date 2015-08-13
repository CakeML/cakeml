open Format

type box_type = H | V | Hv | Hovp | Hovs

type format_decl =
  | Lit of string
  | Box of box_type * int * format_decl list
  | Break of int * int
  | Action of (unit -> unit)
  | Newline

let (%) f g x = f (g x)

let open_box : box_type -> int -> unit = function
  | H -> open_hbox % ignore
  | V -> open_vbox
  | Hv -> open_hvbox
  | Hovp -> open_hovbox
  | Hovs -> open_box

let interp x =
  let rec f = function
    | Lit s -> print_string s
    | Box (ty, indent, xs) ->
      open_box ty indent;
      List.iter f xs;
      close_box ()
    | Break (sp, indent) -> print_break sp indent
    | Action a -> a ()
    | Newline -> print_newline ()
  in
  f x; print_newline ()
