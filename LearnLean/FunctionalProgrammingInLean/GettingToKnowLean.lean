/- Evaluting expressions-/

#eval 1 + 2
#eval 1 + 2 * 5

#eval String.append "Hello, " "Lean!"
#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if false then "yes" else "no")

/- Types -/
#eval (1 + 2 : Nat)
#eval (1 - 2 : Nat)
#eval (1 - 2 : Int)
#check (1 - 2 : Int)

/- Functions and definitions -/
def hello : String := "Hello"
#eval hello

def add1 (n : Nat) : Nat := n + 1
#eval add1 41

def maximum (n : Nat) (m : Nat) : Nat :=
  if n > m then
    n
  else
    m
#eval maximum 10 20
#check (maximum 10)

/- defining types -/
def Str : Type := String
#check (Str)

def NaturalNumber : Type := Nat
def thirtyEight : NaturalNumber := ( 38 : Nat )

abbrev N : Type := Nat
def thirtyNine : N := 39
#check (thirtyNine)

/- Structures -/
#check 1.2
#check -1123.1234124

#check 0
#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y}
def p1 : Point := {x := 3, y := 4}
def p2 : Point := {x := 7, y := 9}
#eval addPoints p1 p2

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p1.x - p2.x)^2.0) + ((p1.y - p2.y)^2.0))
#eval distance p1 p2

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr
def origin3d : Point3D := {x := 0.0, y := 0.0, z := 0.0}

/- Updating structures -/
def zeroX (p : Point) : Point :=
  { p with x := 0}
#eval p1
#eval zeroX p1
