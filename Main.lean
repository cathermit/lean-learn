import Lean.Meta.Tactic.Assumption
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R :=
fun p => h2 (h1 p)

example (A : Prop) : A → A :=
fun p => p

example (A : Prop) : A → A :=
by
intro a
exact a

example (A : Prop) (h : A) : A :=
by
let x : A := h
exact x

-- example (A : Prop) (A) : A := (A) is invalid, no type
-- by
-- exact A

-- example (A B C : Prop) (h : (A → C) ∨ (B → C)) : (A ∨ B) → C :=
-- by
-- intro a
-- exact

example (A B C : Prop) (h : (A ∨ B) → C) : (A → C) ∨ (B → C) :=
Or.inl (fun a => h (Or.inl a))
