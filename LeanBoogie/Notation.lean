
/-- Two imperative programs executed after one another. Provides the `;; ` notation. -/
class Seqi (A : Type) where
  seqi : A -> A -> A
infixl:20 ";; " => Seqi.seqi

/-- Concatenation of continuations. Provides the `>>>` notation. -/
class Cat (K : Type -> Type -> Type) where
  cat : K A B -> K B C -> K A C
infixl:75 " >>> " => Cat.cat
