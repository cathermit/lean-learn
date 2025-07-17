open Nat

-- there are terms – they can be constants, variables, functions, proofs
-- there are expressions – they can be terms or code that evaluates to a term
-- there are statements – they declare variables, functions, theorems, examples (start with def, example, theorem)

#eval (if 3 == 3 then 5 else 7 : Int)

-- definition syntax for variables
def hi : String := "Hey"

-- definition syntax for functions
def process (n : Nat) (m : String) : Bool :=
  if m.length < n then True else False

#eval process 1 "yo"

  -- a function f with multiple arguments A : Type1, B : Type2 that returns a term of Type3 is of type f : Type1 → (Type2 → Type3) -- ≣ Type1 → Type2 → Type3

#check process --return function signature
#check (process) -- return function type
#check 1 --return expression type

--defining types
def sss : Type := String → String → String --here, b is a term of type Type and value String → String → String
-- another way for definition of functions
def join : sss := fun x y => x ++ y
#eval join "s" "o"


-- Structures

structure point where
  x : Nat
  y : Nat
deriving Repr --to indicate that #eval anypoint shows the values of x and y

def origin : point := {x := 0, y := 0}

def pointsum (p1 : point) (p2 : point) : point :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

def xchange (p : point) : point :=
  {p with x := 1}

#eval origin
#eval xchange origin
#eval origin    --function returns different point than origin

#check point.mk 1 2 --mk (as in make?) is a constructor
#check point.mk
#check (point.mk)

structure pointc where
  point1::
  x : Nat
  y : Nat
deriving Repr

#check (pointc.point1 1 2) --constructor name

#check point.x -- accessor functions and point is the accessor of the structure point

#eval "a".append "b"

--inductive types
inductive list where
  |φ : list -- a constructor to start with
  |element : Nat → list → list -- another constructor of the type list (since these are all constructors of inductive types, the functions return the same type)
deriving Repr

inductive set where
  |φ : set -- a constructor to start with
  |suc : set → set -- another constructor of the type list (since these are all constructors of inductive types, the functions return the same type)
deriving Repr

def four : list := list.element 1 (list.element 2 (list.element 3 (list.element 4 list.φ)))
#eval four

def two : set := set.suc (set.suc set.φ)
#eval two

-- inductive line where
--   |φ : line
--   |element : Nat → line
-- deriving Repr

--def two : line := line.element (line.element 1)

def isempty (n : list) : Bool :=
  match n with
  | list.φ => true
  | list.element (_ : Nat) (_ : list) => false

#eval isempty list.φ
#eval isempty (list.element 1 list.φ)

def is_even (n : set) : Bool :=
match n with
  |set.φ => true
  |set.suc k => not (is_even k)

def max (m : set) (n : set) : set :=
  match m, n with
  |set.φ, (a : set) => a
  |(a : set), set.φ => a
  |(set.suc m1), (set.suc n1) => set.suc (max m1 n1)

def plus (m : set) (n : set) : set :=
  match m, n with
  |set.φ, (a : set) => a
  |(a : set), set.φ => a
  |a, set.suc b => plus (set.suc a) b

def multiply (m : set) (n : set) : set :=
  match m, n with
  |set.φ, _ => set.φ
  |_, set.φ => set.φ
  |set.suc set.φ, a => a
  |a, set.suc set.φ => a
  |a, set.suc b => multiply (plus a a) b

--polymorphic structures
structure typepoint (α : Type) where
  typepoint::
  x : α
  y : α
deriving Repr

def nullpoint : typepoint set :=
  {x := set.φ, y := set.φ}

def replace (α : Type) (p : typepoint α) (q : typepoint α) : typepoint α:=
  {p with x := q.x, y := q.y}

#eval replace Nat {x := 0, y := 1} {x := 2, y := 3}
#eval replace set nullpoint {x := two, y := set.suc set.φ}

inductive sign where
  |positive -- can also add : sign
  |negative
  |null
deriving Repr

def checkparity (n : Int) : sign :=
  if n == 0 then
    sign.null
  else if n > 0 then
    sign.positive
  else
    sign.negative

#eval (checkparity 1)

inductive typelist (α : Type) where
  |φ : typelist α
  |next : α -> typelist α -> typelist α
deriving Repr

def length (α : Type) (l : typelist α) : Nat :=
  match l with
  |typelist.φ => 0
  |typelist.next _ b => 1 + (length α b)

#eval length Nat (typelist.next 10 (typelist.next 1 typelist.φ))

def list.head (α : Type) (l : typelist α) : Option α :=
  match l with
  |typelist.φ => none
  |typelist.next a _ => some a

#eval list.head Nat (typelist.next 10 (typelist.next 1 typelist.φ))
#check (list.head Nat (typelist.next 10 (typelist.next 1 typelist.φ)))

-- inductive Option (α : Type) : Type where
--   | none : Option α
--   | some (val : α) : Option α -- which can be written also as α -> Option α

structure prod (α : Type) (β : Type) where
  x : α
  y : β

def three : prod Nat String := {x := 3, y := "three"}

#eval three.y

--there is a library structure Prod which can also be called with α ⨯ β

inductive sum (α : Type) (β : Type) : Type where
  |inl : α → sum α β
  |inr : β → sum α β

--there is a structure Sum which can also be called with α ⊕ β
-- it is like an enum

--function to find the last entry in a list. It should return an Option
def last (α : Type) (l : List α) : Option α :=
  match l with
  |[] => none
  |a :: [] => some a -- [a] also okay
  |_ :: remaining => last α remaining

--a function that finds the first entry in a list that satisfies a given predicate
def List.findFirst? {α : Type} (l : List α) (predicate : α → Bool) : Option α :=
  match l with
  |[] => none
  |a :: remaining => if predicate a then some a else List.findFirst? remaining predicate

--a function Prod.swap that swaps the two fields in a pair.
def prod.swap {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)


--a function zip that combines two lists into a list of pairs.
def zip {α : Type} {β : Type} (a : List α) (b : List β) : List (α × β) :=
  match a,b with
  |[],[] => []
  |[],_ => []
  |_,[] => []
  |x :: rema, y :: remb => (x,y) :: zip rema remb


--a polymorphic function take that returns the first n entries in a list, where n is a Nat. If the list contains fewer than n entries, then the resulting list should be the input list
def take {α : Type} (n : Nat) (l : List α) : List α :=
  match n,l with
  |0, _ => []
  |_,[] => []
  |n, (a :: rem) => a :: take (n - 1) (rem)


--a function that distributes products over sums (both have same size)
def distribute {α β γ : Type} (x : (α × (β ⊕ γ))) : (α × β) ⊕ (α × γ) :=
  match x with
  |(a, Sum.inl b) => Sum.inl (a, b)
  |(a, Sum.inr c) => Sum.inr (a, c)


--both have the same size
def twice {α : Type} : Bool × α → α ⊕ α
  |(true, a) => Sum.inl a
  |(false, a) => Sum.inl a


namespace names
def rep (a : String) : String := a.append a
end names

#eval names.rep "ab"
#eval s!"!! {names.rep "hi"}"

#eval (·  - 1) 2

#eval (3)
