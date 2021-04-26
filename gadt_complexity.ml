type zero = [`Zero]

type 'a succ = [`Succ of 'a]

type 'a nat =
  | O : zero nat
  | S : 'a nat -> 'a succ nat

type ('a, 'b, 'c) plus =
  | PO : (zero, 'a, 'a) plus
  | PS : ('a, 'b, 'c) plus -> ('a succ, 'b, 'c succ) plus

type ('a, 'b, 'c) cursor =
  | CO : (zero, 'a, 'a) cursor
  | CS : ('a, 'b succ, 'c) cursor -> ('a succ, 'b, 'c) cursor

type ('a, 'b) eq = Refl : ('a, 'a) eq

let cast (type a b) (Refl : (a, b) eq) (x : a) : b = x

let sym (type a b) (Refl : (a, b) eq) : (b, a) eq = Refl

let eq_cursor2 (type a b c d) (Refl : (b, d) eq) :
    ((a, b, c) cursor, (a, d, c) cursor) eq = Refl

let rec nat_of_cursor : type a b c . (a, b, c) cursor -> a nat = function
  | CO -> O
  | CS c -> S (nat_of_cursor c)

let rec nat_of_plus : type a b c . (a, b, c) plus -> a nat = function
  | PO -> O
  | PS c -> S (nat_of_plus c)

module type TypeS = sig
  type 'a t

  val commut : ('a succ t, 'a t succ) eq
end

module type PlusOfCursorS = sig
  type n

  module Make (X : TypeS) : sig
    type ('a, 'b) convert =
        Exists : ('b, 'c X.t) eq * (n, 'a, 'c) plus -> ('a, 'b) convert
    val convert : (n, 'a X.t, 'b) cursor -> ('a, 'b) convert
  end
end

let rec plus_of_cursor_aux : type n .
  n nat -> (module PlusOfCursorS with type n = n) = fun n ->
  match n with
  | O ->
      let module PlusOfCursor = struct
        type n = zero
        module Make (X : TypeS) = struct
          type ('a, 'b) convert =
              Exists : ('b, 'c X.t) eq * (n, 'a, 'c) plus -> ('a, 'b) convert
          let convert (type a b) (CO : (n, a X.t, b) cursor) :
              (a, b) convert =
            Exists (Refl, PO)
        end
      end in
      (module PlusOfCursor)
  | S n' ->
      let (module PlusOfCursor') = plus_of_cursor_aux n' in
      let module PlusOfCursor = struct
        type nonrec n = n
        module Make (X : TypeS) = struct
          type ('a, 'b) convert =
              Exists : ('b, 'c X.t) eq * (n, 'a, 'c) plus -> ('a, 'b) convert
          let convert (type a b) (CS cursor' : (n, a X.t, b) cursor) :
              (a, b) convert =
            let module X' = struct
              type 'a t = 'a succ X.t
              let commut = X.commut
            end in
            let module C = PlusOfCursor'.Make (X') in
            let Exists (Refl, plus) =
              C.convert (cast (eq_cursor2 (sym X.commut)) cursor') in
            Exists (Refl, PS plus)
        end
      end in
      (module PlusOfCursor)

let plus_of_cursor (type a b c) (cursor : (a, b, c) cursor) : (a, b, c) plus =
  let (module PlusOfCursor) = plus_of_cursor_aux (nat_of_cursor cursor) in
  let module X = struct
    type 'a t = 'a
    let commut = Refl
  end in
  let module C = PlusOfCursor.Make (X) in
  let Exists (Refl, plus) = C.convert cursor in
  plus

module type CursorOfPlusS = sig
  type n

  module Make (X : TypeS) : sig
    val convert : (n, 'a, 'b) plus -> (n, 'a X.t, 'b X.t) cursor
  end
end

let rec cursor_of_plus_aux : type n .
  n nat -> (module CursorOfPlusS with type n = n) = fun n ->
  match n with
  | O ->
      let module CursorOfPlus = struct
        type n = zero
        module Make (X : TypeS) = struct
          let convert (type a b) (PO : (n, a, b) plus) :
              (n, a X.t, b X.t) cursor =
            CO
        end
      end in
      (module CursorOfPlus)
  | S n' ->
      let (module CursorOfPlus') = cursor_of_plus_aux n' in
      let module CursorOfPlus = struct
        type nonrec n = n
        module Make (X : TypeS) = struct
          let convert (type a b) (PS plus' : (n, a, b) plus) :
              (n, a X.t, b X.t) cursor =
            let module X' = struct
              type 'a t = 'a succ X.t
              let commut = X.commut
            end in
            let module C = CursorOfPlus'.Make (X') in
            let cursor = C.convert plus' in
            CS (cast (eq_cursor2 X.commut) cursor)
        end
      end in
      (module CursorOfPlus)

let cursor_of_plus (type a b c) (plus : (a, b, c) plus) : (a, b, c) cursor =
  let (module CursorOfPlus) = cursor_of_plus_aux (nat_of_plus plus) in
  let module X = struct
    type 'a t = 'a
    let commut = Refl
  end in
  let module C = CursorOfPlus.Make (X) in
  C.convert plus

let rec plus_zero_r : type n . n nat -> (n, zero, n) plus = function
  | O -> PO
  | S n' -> PS (plus_zero_r n')

let cursor_zero_r (type n) (n : n nat) : (n, zero, n) cursor =
  cursor_of_plus (plus_zero_r n)

let rec cursor_commut :
type a b c . b nat -> (a, b, c) cursor -> (b, a, c) cursor = fun b cursor ->
  match cursor with
  | CO -> cursor_zero_r b
  | CS cursor' ->
      let CS cursor'' = cursor_commut (S b) cursor' in
      cursor''

let plus_commut (type a b c) (b : b nat) (plus : (a, b, c) plus)
    : (b, a, c) plus =
  plus_of_cursor (cursor_commut b (cursor_of_plus plus))
