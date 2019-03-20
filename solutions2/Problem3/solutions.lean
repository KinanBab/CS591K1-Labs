@[simp] def mylength : (list nat) -> nat
| list.nil := 0
| (list.cons h l') := 1 + mylength l'

-- Problem 3: reversing a list (35 points for full credit, total with all bonuses is 60 points)

-- Part A: implement a reverse functionality  (5 points)
-- One of the common ways to reverse an array is to rely
-- on append
#check list.append
#eval [1, 2, 3] ++ [6, 7] -- shortcut notation for list.append
@[simp] def myrev : (list nat) -> (list nat)
| list.nil := list.nil
| (list.cons x l) := (myrev l) ++ [x]

-- Part B: simple reverse properties (5 points)
-- Helpful lemma: show how myrev and append compose
lemma myrev_append (l1 l2: list nat) :
  myrev (l1 ++ l2) = (myrev l2) ++ (myrev l1) :=
begin
  induction l1,
    simp,

    simp,
    rewrite l1_ih,
    apply list.append_assoc,
end

-- applying reverse twice should land us in the same array
theorem myrev_myrev (l: list nat) :
  myrev (myrev l) = l :=
begin
  induction l,
    simp,

    simp,
    rewrite myrev_append,
    simp,
    assumption,
end

-- Part B: reverse and length (5 points)
-- show how length and append compose
lemma mylength_append (l1 l2: list nat):
  mylength (l1 ++ l2) = mylength l1 + mylength l2 :=
begin
  induction l1,
    simp,

    simp,
    rewrite l1_ih,
    simp,
end

-- reverse preserves length
theorem myrev_length (l: list nat):
  mylength l = mylength (myrev l) :=
begin
  induction l,
    simp,

    simp,
    rewrite l_ih,
    rewrite mylength_append,
    simp,
end

-- Part C: (10 points)
-- Are these 2 theorems (without the lemmas) enough to conclude
-- that myrev is `correct` according to our intuitive definition of correctness?
-- Can you think of a counter example implementation?
-- one that satisifies both properties but is incorrect?
-- HINT: you can come up with one without using append
@[simp] def incorrect_myrev : (list nat) -> (list nat)
| l := l

theorem incorrect_myrev_ok1 (l: list nat) :
  incorrect_myrev (incorrect_myrev l) = l :=
begin
  simp,
end

theorem incorrect_myrev_ok2 (l: list nat) :
  mylength l = mylength (incorrect_myrev l) :=
begin
  simp,
end

-- Part D: BONUS (10 points)
-- What if we include myrev_append lemma? how about only [myrev_append] lemma and [myrev_length]?
-- Would your counter example still work?
-- If yes, prove it! can you give another counter example?
-- if not, how can you be sure that no other example exists?
-- Write a theorem statement that formally encodes whether the
-- properties are enough or not, you do not have to prove it (but can do so for an extra 15 points)
-- HINT: one possible way of encoding this is to say, if myrev satisifies both theorems, then
--       it must satisify some very tedious and verbose encoding of what `correctness` means.
theorem total_correctness (myrev: list nat → list nat) :
  -- Previous theorem statements
  (∀{l1 l2: list nat}, myrev (l1 ++ l2) = (myrev l2) ++ (myrev l1))
  → (∀{l: list nat}, myrev (myrev l) = myrev l)
  → (∀{l: list nat}, mylength l = mylength (myrev l))
  -- Correctness
  → ∀{l: list nat}{i: nat}, i < (mylength l) → (list.nth l i) = (list.nth (myrev l) ((mylength l) - i)) :=
begin
  admit,
end

-- Part E: summing the elment of the list (10 points)
@[simp] def mysum : (list nat) -> nat
| list.nil := 0
| (list.cons x l) := x + (mysum l)

-- It may help you to prove some lemma about mysum and append
-- in particular that the sum of two appended list, is the
-- sum of each separatly added together
-- you can use such a lemma in the theorem below to simplify the proof.

lemma append_mysum (l1 l2: list nat) :
  mysum (l1 ++ l2) = (mysum l1) + (mysum l2) :=
begin
  induction l1,
    simp,

    simp,
    rewrite l1_ih,
    simp,
end

-- prove that reverse preserves sum
theorem myrev_mysum (l1: list nat) :
  mysum (myrev l1) = mysum l1 :=
begin
  induction l1,
    simp,

    simp,
    rewrite append_mysum,
    rewrite l1_ih,
    simp,
end
