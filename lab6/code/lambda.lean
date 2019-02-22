-- Syntax
inductive term
| var  : string  → term
| abs  : string → term → term
| app  : term → term → term

-- Custom notation
instance : has_coe string term := ⟨term.var⟩
notation `λ:`x `.` t := term.abs x t
notation `[`t1`](`t2`)` := term.app t1 t2

-- Substitution: the core of beta reduction
@[simp] def substitute : term -> string -> term -> term
| t v (term.var x) :=
    if to_bool (x = v) then t else (term.var x)
| t v (term.abs x t') :=
    if to_bool (x = v) then (term.abs x t') else (term.abs x (substitute t v t'))
| t v (term.app t1 t2) :=
    term.app (substitute t v t1) (substitute t v t2)

-- reflexive transative closure
inductive rStar {T} (rel: T -> T -> Prop) : T -> T -> Prop
| base : ∀ {t}, rStar t t
| trans {t1 t2 t3} : rel t1 t2 -> rStar t2 t3 -> rStar t1 t3

-- beta reduction
inductive beta : term -> term -> Prop
| appl: ∀{t1 t1' t2: term},
       beta t1 t1'
       -> beta (term.app t1 t2) (term.app t1' t2) 
| appr: ∀{t1 t2 t2': term},
       beta t2 t2'
       -> beta (term.app t1 t2) (term.app t1 t2')
| app :∀{x: string}, ∀{t1 t2: term},
       beta (term.app (term.abs x t1) t2) (substitute t2 x t1)

notation t `→β`:45 t' := beta t t'
notation t `↠β`:45 t' := (rStar beta) t t'

-- What is a value?
inductive value : term -> Prop
| var: ∀{x}, value (term.var x)
| abs: ∀{x t}, value (term.abs x t)

-- Our simple types
inductive type
| dot  -- dot or constant type
| func: type -> type -> type -- function type: has domain and range types

-- Our typing rules
def env := list (string × type)
instance : has_append env := ⟨list.append⟩
@[simp] def type_from_env : env -> string -> type -> type
| list.nil v default := default
| (list.cons (x, t) env') v default :=
  if to_bool (v = x) then t else type_from_env env' v default

inductive typing : env -> term -> type -> Prop
| var: ∀{E x t},
       (type_from_env E x type.dot) = t
       -> typing E (term.var x) t
| abs: ∀{E x t1 b t2},
       typing (list.cons (x, t1) E) b t2
       -> typing E (term.abs x b) (type.func t1 t2)
| app: ∀{E term1 t1 term2 t2}, 
       typing E term1 (type.func t1 t2)
       -> typing E term2 t1
       -> typing E (term.app term1 term2) t2


