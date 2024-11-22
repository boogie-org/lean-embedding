
/-- Two imperative programs executed after one another. Provides the `;; ` notation. -/
class Seqi (A : Type) where
  seqi : A -> A -> A
infixl:20 ";; " => Seqi.seqi

/-- Concatenation of continuations. Provides the `>>>` notation. -/
class Cat (K : Type -> Type -> Type) where
  cat : K A B -> K B C -> K A C
infixl:75 " >>> " => Cat.cat

/-- Monad morphism from a computation monad `M` to a specification monad `W`. -/
class Theta (M : Type -> Type) (W : outParam (Type -> Type)) where
  θ : M A -> W A
export Theta (θ)

class LawfulTheta (M : (Type -> Type)) [m : Monad M] (W : outParam (Type -> Type)) [w : Monad W] [Theta M W] : Prop where
  θ_pure : θ (m.pure a) = w.pure a
  θ_bind : θ (m.bind a b) = w.bind (θ a) (fun a => θ (b a))

export LawfulTheta (θ_pure θ_bind)
