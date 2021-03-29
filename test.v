Module Base.
Inductive t :=
| A
| B.

Definition f0 x :=
  match x with
  | A => A
  | B => B
  end.

Print f0.

Definition f0bis x y :=
  match x, y with
  | A, A => A
  | _, _ => B
  end.

Print f0bis.
End Base.

Definition f1 n :=
  match n with
  | O => Base.A
  | S _ => Base.B
  end.

Print f1.

Definition f2 n :=
  match n with
  | O => Base.A
  | S (S n) => Base.B
  | _ => Base.A
  end.

Print f2.

Definition pred n :=
  match n with
  | O => O
  | S O => O
  | S (S n) => S n
  end.

Print pred.

Fixpoint add n m :=
  match n, m with
  | O, _ => m
  | _, O => n
  | S p, S q => S (S (add p q))
  end.

Print add.

Theorem add_0_l n : add O n = n.
Proof.
reflexivity.
Qed.

Inductive vector (A : Type) : nat -> Type :=
| Nil : vector A O
| Cons n (_ : A) (_ : vector A n) : vector A (S n).

Definition rectS {A} (P:forall {n}, vector A (S n) -> Type)
 (bas: forall a: A, P (Cons _ _ a (Nil _)))
 (rect: forall a {n} (v: vector A (S n)), P v -> P (Cons _ _ a v)) :=
 fix rectS_fix {n} (v: vector A (S n)) : P v :=
 match v with
 |Cons _ 0 a v =>
   match v with
     |Nil _ => bas a
     |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
   end
 |Cons _ (S nn') a v => vector_rect a v (rectS_fix v)
 |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
 end.

Definition head' (A : Type) (n : nat) (v : vector A (S n)) :=
  match v in vector _ n0 return match n0 return Type with
  | S m => A
  | O => IDProp
  end with
  | Cons _ _ hd _tl => hd
  | Nil _ => idProp
  end.

Print head'.

Definition head (A : Type) (n : nat) (v : vector A (S n)) :=
  match v with
  | Cons _ _ hd _tl => hd
  end.

Print head.

Definition tail' (A : Type) (n : nat) (v : vector A (S n)) : vector A n :=
  match v in vector _ n0 return match n0 return Type with
  | S m => vector A m
  | O => IDProp
  end with
  | Cons _ _ _hd tl => tl
  | Nil _ => idProp
  end.

Print tail'.

Definition tail (A : Type) (n : nat) (v : vector A (S n)) : vector A n (*bug!*) :=
  match v with
  | Cons _ _ _hd tl => tl
  end.

Print tail.

Definition tail2' (A : Type) (n : nat) (v : vector A (S (S n))) :=
   match
     v as v0 in (vector _ H)
     return
       (match H as H0 return Type with
        | O => IDProp
        | S x =>
            match x as H1 return Type with
            | O => IDProp
            | S x0 => vector A (S x0)
            end
        end)
   with
   | Nil _ => idProp
   | Cons _ x _hd tl =>
       match x as H, tl return match H return Type with
         | O => IDProp
         | S n => vector A (S n)
       end with
       | O, _ => idProp
       | S x0, tl => tl
       end
   end.

Print tail2'.

Definition tail2 (A : Type) (n : nat) (v : vector A (S (S n))) :=
  match v with
  | Cons _ _ _hd tl => tl
  end.

Print tail2.

Definition snd (A : Type) (n : nat) (v : vector A (S (S n))) :=
  match v with
  | Cons _ _ _ (Cons _ _ hd _) => hd
  end.

Print snd.

Definition third (A : Type) (n : nat) (v : vector A (S (S (S n)))) :=
  match v with
  | Cons _ _ _ (Cons _ _ _ (Cons _ _ hd _)) => hd
  end.

Print third.

Definition forth (A : Type) (n : nat) (v : vector A (S (S (S (S n))))) :=
  match v with
  | Cons _ _ _ (Cons _ _ _ (Cons _ _ _ (Cons _ _ hd _))) => hd
  end.

Print forth.

Definition fifth (A : Type) (n : nat) (v : vector A (S (S (S (S (S n)))))) :=
  match v with
  | Cons _ _ _ (Cons _ _ _ (Cons _ _ _ (Cons _ _ _ (Cons _ _ hd _)))) => hd
  end.

Print fifth.

Fixpoint map A B (n : nat) (f : A -> B) (v : vector A n) : vector B n :=
  match v with
  | Nil _ => Nil B
  | Cons _ _ hd tl => Cons _ _ (f hd) (map _ _ _ f tl)
  end.

Print map.

(*
Fixpoint mapn A B (n : nat) (f : A -> B) (v : vector A n) : vector B n :=
  match n, v with
  | O, Nil _ => Nil B
  | S m, Cons _ _ hd tl => Cons _ _ (f hd) (mapn _ _ m f tl)
  end.

Print mapn.
*)

Fixpoint map2' A0 A1 B (n : nat) (f : A0 -> A1 -> B) (v0 : vector A0 n) (v1 : vector A1 n) :=
  match v0 in vector _ n0 return
    vector A1 n0 -> vector B n0
 with
  | Nil _ => fun v1 : vector A1 O =>
     match v1 in vector _ n0 return
       match n0 return Type with
       | O => vector B O
       | S _ => IDProp
       end with
     | Nil _ => Nil B
     | Cons _ _ _ _ => idProp
     end
  | Cons _ n0 hd0 tl0 => fun v1 : vector A1 (S n0) =>
     match v1 in vector _ n1 return
       match n1 return Type with
       | O => IDProp
       | S n2 => vector A0 n2 -> vector B (S n2)
     end with
     | Nil _ => idProp
     | Cons _ n1 hd1 tl1 => fun tl0 : vector A0 n1 =>
         Cons _ n1 (*bug!*) (f hd0 hd1) (map2' A0 A1 B _ f tl0 tl1)
     end tl0
  end v1.

Print map2'.

Fixpoint map2 A0 A1 B (n : nat) (f : A0 -> A1 -> B) (v0 : vector A0 n) (v1 : vector A1 n) : vector B n :=
  match v0, v1 with
  | Nil _, Nil _ => Nil _
  | Cons _ _ hd0 tl0, Cons _ _ hd1 tl1 =>
    Cons _ _ (f hd0 hd1) (map2 _ _ _ _ f tl0 tl1)
  end.

Print map2.

Module M0.
Inductive t : nat -> Type :=
| A : t (S O).

Definition test := fun n (v : t n) =>
match n, v with
| S n, A => tt
end.
End M0.

Module M1.
Inductive t : nat -> Type := C : t 0 | D n : t n -> t n.

Definition test (v : t 0) : t 0 :=
match v with
| C => C
| D _ x => x
end.

Print test.
End M1.


(*
Fixpoint map3 A0 A1 A2 B (n : nat) (f : A0 -> A1 -> A2 -> B) (v0 : vector A0 n) (v1 : vector A1 n) (v2 : vector A2 n) : vector B n :=
  match v0, v1, v2 with
  | Nil _, Nil _, Nil _ => Nil _
  | Cons _ _ hd0 tl0, Cons _ _ hd1 tl1, Cons _ _ hd2 tl2 =>
    Cons _ _ (f hd0 hd1 hd2) (map3 _ _ _ _ _ f tl0 tl1 tl2)
  end.

Print map3.
*)
(* from Logic.v *)

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex A P.

Section Projections.

  Variables (A:Prop) (P:A->Prop).

  Definition ex_proj1 (x:ex A P) : A :=
    match x with ex_intro _ _ a _ => a end.

  Print ex_proj1.

  Definition ex_proj2 (x:ex A P) : P (ex_proj1 x) :=
    match x with ex_intro _ _ _ b => b end.

End Projections.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Definition andb (b1 b2:bool) : bool := if b1 then b2 else false.

Require Import Lists.List.

Import ListNotations.

  Fixpoint last (A: Type) (l:list A) (d:A) : A :=
  match l with
    | [] => d
    | [a] => a
    | a :: l => last A l d
  end.

Section Equivalences.

  Variable U:Type.

  Definition UIP_refl_on_ (x : U) :=
    forall (p : x = x), p = eq_refl x.

End Equivalences.

Theorem UIP_shift_on (X : Type) (x : X) :
  UIP_refl_on_ X x -> forall y : x = x, UIP_refl_on_ (x = x) y.
Proof.
  intros UIP_refl y.
  rewrite (UIP_refl y).
  intros z.
  assert (UIP:forall y' y'' : x = x, y' = y'').
  { intros. apply eq_trans_r with (eq_refl x); apply UIP_refl. }
  transitivity (eq_trans (eq_trans (UIP (eq_refl x) (eq_refl x)) z)
                         (eq_sym (UIP (eq_refl x) (eq_refl x)))).
  - destruct z. destruct (UIP _ _). reflexivity.
  - change
      (match eq_refl x as y' in _ = x' return y' = y' -> Prop with
       | eq_refl => fun z => z = (eq_refl (eq_refl x))
       end (eq_trans (eq_trans (UIP (eq_refl x) (eq_refl x)) z)
                     (eq_sym (UIP (eq_refl x) (eq_refl x))))).
    destruct z. destruct (UIP _ _). reflexivity.
Qed.

Lemma UIP_refl_bool (b:bool) (x : b = b) : x = eq_refl.
Proof.
  destruct b.
  - change (match true as b return true=b -> Prop with
            | true => fun x => x = eq_refl
            | _ => fun _ => True
            end x).
    destruct x; reflexivity.
  - change (match false as b return false=b -> Prop with
            | false => fun x => x = eq_refl
            | _ => fun _ => True
            end x).
    destruct x; reflexivity.
Defined.

Module Fin.
Inductive t : nat -> Set :=
|F1 : forall {n}, t (S n)
|FS : forall {n}, t n -> t (S n).

Definition case0 P (p: t O): P p :=
  match p with | F1 | FS  _ => fun devil => False_rect (@IDProp) devil (* subterm !!! *) end.

Definition caseS' {n : nat} (p : t (S n)) : forall (P : t (S n) -> Type) 
  (P1 : P F1) (PS : forall (p : t n), P (FS p)), P p :=
  match p with
  | @F1 k => fun P P1 PS => P1
  | FS pp => fun P P1 PS => PS pp
  end.

Fixpoint weak {m}{n} p (f : t m -> t n) :
  t (p + m) -> t (p + n) :=
match p as p' return t (p' + m) -> t (p' + n) with
  |0 => f
  |S p' => fun x => match x with
     |@F1 n' => fun eq : n' = p' + m => F1
     |@FS n' y => fun eq : n' = p' + m => FS (weak p' f (eq_rect _ t y _ eq))
  end (eq_refl _)
end.

End Fin.
