
/-- Two imperative programs executed after one another. Provides the `;; ` notation. -/
class Seqi (A : Type u) where
  seqi : A -> A -> A
infixl:20 ";; " => Seqi.seqi

/-- Concatenation of continuations. Provides the `>>>` notation. -/
class Cat (K : Type u -> Type u -> Type u) where
  cat : K A B -> K B C -> K A C
infixl:75 " >>> " => Cat.cat

/-- Monad morphism from a computation monad `M` to a specification monad `W`. -/
class Theta (M : Type u -> Type u) (W : outParam (Type u -> Type u)) where
  θ : M A -> W A
export Theta (θ)

class LawfulTheta (M : (Type u -> Type u)) [m : Monad M] (W : outParam (Type u -> Type u)) [w : Monad W] [Theta M W] : Prop where
  θ_pure : θ (m.pure a) = w.pure a
  θ_bind : θ (m.bind a b) = w.bind (θ a) (fun a => θ (b a))

export LawfulTheta (θ_pure θ_bind)
