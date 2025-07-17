  class Plus (α : Type) where
    plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

instance : Plus String where
  plus := String.append

inductive set where
  |φ : set -- a constructor to start with
  |suc : set → set -- another constructor of the type list (since these are all constructors of inductive types, the functions return the same type)
deriving Repr

-- instance : Plus set where
--   plus m n :=
--     match m with
--     |set.φ => n
--     |set.suc a => set.suc (Plus.plus a n)

def add (m : set) (n : set) : set :=
  match m with
  |set.φ => n
  |set.suc a => set.suc (add a n)

instance : Plus set where
  plus := add

open Plus --alternatively open Plus (plus)

#eval plus "a" "ha"
#eval plus 1 2
#eval plus (set.suc set.φ) (set.suc set.φ)


class toaster (α : Type) where
 toast : α → String

def toasts (a : set) : String :=
  match a with
  |set.φ => "set.φ"
  |set.suc a => s!"set.suc({toasts a})"

 instance : toaster set where
   toast := toasts

def toastd (n : Nat) : String :=
  match n with
  |1 => "1"
  |2 => "2"
  |3 => "3"
  |4 => "4"
  |5 => "5"
  |6 => "6"
  |7 => "7"
  |8 => "8"
  |9 => "9"
  |0 => "0"
  |_ => "?"

def toastn (n : Nat) : String :=
  if n < 10 then
    toastd n
  else
    toastn (n/10) ++ toastd (n%10)

instance : toaster Nat where
  toast := toastn

-- instance : OfNat String 1 where
--   ofNat := toString 22

#check (OfNat.ofNat)

instance : OfNat String 1 where
  ofNat := "one"

#eval (1 : String)

def pea (n : Nat) : set :=
  match n with
  |0 => set.φ
  |(a + 1) => set.suc (pea a)

instance (n : Nat) : OfNat set n where
  ofNat := pea n -- gpt4 says avoid

#eval (2 : set)

structure positive where
  suc ::
  pred : Nat
--deriving Repr

#eval positive.suc 1

def next (p : positive) :=
  match p with
  |positive.suc a => positive.suc (a+1)

def addp (p q : positive) : positive :=
  match p with
  |positive.suc 0 => q
  |positive.suc (a+1) => addp (positive.suc (a)) (next q)

#eval addp (positive.suc 3) (positive.suc 0)

def mult (p q : positive) : positive :=
  match p with
  |positive.suc 0 => positive.suc 0
  |positive.suc 1 => q
  |positive.suc (a+1) => addp q (positive.suc a)

def post (p : positive) : String :=
  match p with
  |positive.suc a => s!"positive.suc{a}"

def positiveofnat (n : Nat) : positive :=
  positive.suc (n - 1) --sus for n = 0

instance : Add positive where
  add := addp

instance : Mul positive where
  mul := mult

instance : ToString positive where
  toString := post

instance (n : Nat) : OfNat positive n where
  ofNat := positiveofnat n


inductive httpmethod where
  |GET
  |POST
deriving Repr

def methodstring : httpmethod → String
  |httpmethod.GET => "GET"
  |httpmethod.POST => "POST"

instance : ToString httpmethod where
  toString := methodstring

structure httprequest where
  method : httpmethod
  URI : String
  version : String
deriving Repr

def httpstring (h : httprequest) : String :=
  (methodstring h.method) ++ h.URI ++ h.version

instance : ToString httprequest where
  toString := httpstring

#eval IO.println (httprequest.mk httpmethod.GET "a" "b")

instance : ToString set where
  toString := toasts

instance : Add set where
  add := plus

def sets : Array set := #[set.suc set.φ, set.suc (set.suc set.φ)]

#eval sets.sum

def hplus : Nat → set → set
  |0,a => a
  |(a+1),b => hplus a (set.suc b)

def gplus : Nat → set → Nat
  |a,set.φ => a
  |a,set.suc b => gplus (a+1) b

def hplusr (a : set) (b : Nat) : set :=
  hplus b a

instance : HAdd Nat set set where
  hAdd := hplus

instance : HAdd set Nat set where
  hAdd := hplusr

instance : HAdd Nat set Nat where
  hAdd := gplus

#eval 1 + set.φ --only the first instance is chosen

structure point where
  x : Nat
  y : Nat
deriving Repr

/-default types aaa-/

def scalarm (n : Nat) (p : point) : point :=
  {x := n*(p.x), y := n*(p.y)}

instance : HMul Nat point point where
  hMul := scalarm

structure poplist (α : Type) where
  head : α
  tail : List α
deriving Repr

abbrev poplist.inBounds {α : Type} (p : poplist α) (n : Nat) : Prop :=
  n ≤ p.tail.length

def poplist.get {α : Type} (p : poplist α) (n : Nat) (ok : p.inBounds n) : α :=
  match n with
  |0 => p.head
  |i + 1 => p.tail[i]

--indexing overload for collections
-- class GetElem (list : Type) (index : Type) (item : outParam Type) (inBounds : outParam (list → index → Prop)) where
--   getElem : (c : list) → (i : index) → inBounds c i → item

instance {α : Type} : GetElem (poplist α) Nat α poplist.inBounds where
  getElem := poplist.get

def test : poplist Nat := {head := 1, tail := [0,2,3]}

#eval test[1]

def set.toNat : set → Nat
  |set.φ => 0
  |set.suc a => 1 + a.toNat

#eval set.φ.toNat

instance {α : Type} : GetElem (List α) set α (fun l n => l.length > n.toNat) where
  getElem (l : List α) (a : set) proof := l[a.toNat]

#eval [1,2,3][set.φ]
