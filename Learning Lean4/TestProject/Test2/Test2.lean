import Test2.Basic
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m#check n#check n + 0#check m * (n + 0)#check b1-- "&&" is the Boolean and
#check b1 && b2-- Boolean or
#check b1 || b2-- Boolean "true"
#check true/- Evaluate -/

#eval 5 * 4#eval m + 2#eval b1 && b2

/- I'm writing the stuff here to test a declaration-/
def f: Nat → Nat := fun x => x + 1
#eval f 5
def g: Nat → Nat := fun x => x * 2
#eval g 5
#eval f (g 5) -- f(g(5)) = f(10) = 11
#eval f (g 25)

/- Time to try functionals and cartesian products-/
def h: Nat → Nat → Nat := fun x y => x^2 + y^2
#eval h 3 4

/- New copied code:-/
#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2
#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1 /- extracts the first component -/
#eval (5, 9).2 /- extracts the second component -/

/- checking types -/
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

#check Prod

/- Using lambda functions-/
#eval (λ x : Nat => x + 5) 15 -- lambda and function mean the same thing

/- Note: Lean is a complete programming language.
It has a compiler that generates a binary executable and an interactive interpreter.
You can use the command #eval to execute expressions,
and it is the preferred way of testing your functions.-/

def double (x : Nat) : Nat := -- the name is 'double', input type is Nat, output type is Nat
  x + x
/- The following does the same thing: -/
def double2 :=
  fun (x : Nat) => x + x

/- even more doubling and then some-/
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 2) (5 + 7)

/- A good rule is to type-annotate for definitions and functions-/
def Pavlov (x  y n: Nat) : Nat :=
  (x+y)^n

#check Pavlov
#eval Pavlov 2 3 4

/- onto if thens -/
def greater (x y : Nat) : Nat :=
  if x > y then x
  else y

#check greater
#eval greater 5 10

/- Time for function composition -/
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check compose -- Note that compose with the type notation requires us to know information about both functions' types, f and g.

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3 -- all types are Nat, square 3 first, double the result.

/- Using let as a local definition setter.  -/
#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y
def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y -- Oh, I like it in here.

#eval twice_double 3

/- Time for variables: -/
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose1 := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose1
#print doTwice
#print doThrice

/- Because the scope of a variable is the entire file, it helps to limit it to sections-/
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose2 := g (f x)
  def doTwice1 := h (h x)
  def doThrice1 := h (h (h x))
end useful

/- A namespace is a place to store lots of local definitions.  I like that. -/

namespace Foo
  def a : Nat := 5
  def t (x : Nat) : Nat := x + 7

  def fa : Nat := t a
  def ffa : Nat := t (t a)

  #check a
  #check t
  #check fa
  #check ffa
  #check Foo.fa
  end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.t
#check Foo.fa
#check Foo.ffa

open Foo -- This means now I can refer to Foo's definitions without the Foo. prefix

#check a
#check t
#check fa
#check Foo.fa

/- I sometimes think that a namespace is like a preamble in latex -/
-- The following is a cartesian product only needing to declare the type once:
section cartesian_products
universe u v

def p (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def q (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (p Type (fun α => α) Nat x).2

#check p
#check q
#eval h1 5

def h2 (x : Nat) : Nat :=
  (q Type (fun α => α) Nat x).2

#eval h2 5
end cartesian_products
