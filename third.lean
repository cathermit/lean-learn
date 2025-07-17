theorem twothreefive : 2 + 3 = 5 := by
rfl --reflexivity (a = a)

theorem twothreefivesimp : 2 + 3 = 5 := by
simp --simplify (RHS : 2 + 3 => 5 = 5 : LHS)

def hihi : Prop :=
"Hello, ".append "world" = "Hello, world"

theorem hihiyes : hihi :=
rfl

theorem hihitwothreefive : (2 + 3 = 5) ∧ hihi :=
And.intro rfl hihiyes

theorem foo (A B : Prop) : A ∧ B → A :=
  fun h =>
    match h with
    |And.intro a _ => a

theorem fooo (A B : Prop) : A ∧ B → A ∨ B :=
  fun h =>
    match h with
    |And.intro a _ => Or.inl a



theorem foot (A B : Prop) : A ∧ B → A := by
  intro h
  cases h with
  | intro a b => exact a

theorem fooot (A B : Prop) : A ∧ B → A ∨ B := by
  intro h
  cases h with
  | intro a _ => exact Or.inl a

def fif {α : Type} (l : List α) (test : l.length >= 5) : α := l[4]

#eval fif [1, 2, 3, 4, 5] (by simp)
