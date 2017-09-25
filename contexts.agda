open import Prelude
open import List
open import Nat

module contexts where
  -- variables are named with naturals in ė. therefore we represent
  -- contexts as functions from names for variables (nats) to possible
  -- bindings.
  _ctx : Set → Set
  A ctx = Nat → Maybe A

  -- convenient shorthand for the (unique up to fun. ext.) empty context
  ∅ : {A : Set} → A ctx
  ∅ _ = None

  infixr 100 ■_

  -- membership, or presence, in a context
  _∈_ : {A : Set} (p : Nat × A) → (Γ : A ctx) → Set
  (x , y) ∈ Γ = (Γ x) == Some y

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : {A : Set} (n : Nat) → (Γ : A ctx) → Set
  x # Γ = (Γ x) == None

  -- disjointness for contexts
  _##_ : {A : Set} → A ctx → A ctx → Set
  _##_ {A} Γ Γ'  = ((n : Nat) (a : A) → Γ n == Some a → Γ' n == None) ×
                   ((n : Nat) (a : A) → Γ' n == Some a → Γ n == None)

  -- without: remove a variable from a context
  _/_ : {A : Set} → A ctx → Nat → A ctx
  (Γ / x) y with natEQ x y
  (Γ / x) .x | Inl refl = None
  (Γ / x) y  | Inr neq  = Γ y

  -- a variable is apart from any context from which it is removed
  aar : {A : Set} → (Γ : A ctx) (x : Nat) → x # (Γ / x)
  aar Γ x with natEQ x x
  aar Γ x | Inl refl = refl
  aar Γ x | Inr x≠x  = abort (x≠x refl)

  -- contexts give at most one binding for each variable
  ctxunicity : {A : Set} → {Γ : A ctx} {n : Nat} {t t' : A} →
               (n , t) ∈ Γ →
               (n , t') ∈ Γ →
               t == t'
  ctxunicity {n = n} p q with natEQ n n
  ctxunicity p q | Inl refl = someinj (! p · q)
  ctxunicity _ _ | Inr x≠x = abort (x≠x refl)

  -- warning: this is union but it assumes WITHOUT CHECKING that the
  -- domains are disjoint.
  _∪_ : {A : Set} → A ctx → A ctx → A ctx
  (C1 ∪ C2) x with C1 x
  (C1 ∪ C2) x | Some x₁ = Some x₁
  (C1 ∪ C2) x | None = C2 x

  -- the singleton context
  ■_ : {A : Set} → (Nat × A) → A ctx
  (■ (x , a)) y with natEQ x y
  (■ (x , a)) .x | Inl refl = Some a
  ... | Inr _ = None

  -- add a new binding to the context, clobbering anything that might have
  -- been there before.
  _,,_ : {A : Set} → A ctx → (Nat × A) → A ctx
  (Γ ,, (x , t)) = Γ ∪ (■ (x , t))

  infixl 10 _,,_

  -- x∈sing Γ n x with Γ n
  -- x∈sing Γ n x  | Some y with natEQ n n
  -- x∈sing Γ n x₁ | Some y | Inl refl = {!!}
  -- x∈sing Γ n x₁ | Some y | Inr x = abort (x refl)
  -- x∈sing Γ n x  | None with natEQ n n
  -- x∈sing Γ n x₁ | None | Inl refl = refl
  -- x∈sing Γ n x₁ | None | Inr x = abort (x refl)

  x∈∪1 : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ → (n , x) ∈ (Γ ∪ Γ')
  x∈∪1 Γ Γ' n x xin with Γ n
  x∈∪1 Γ Γ' n x₁ xin | Some x = xin
  x∈∪1 Γ Γ' n x ()   | None

  -- x∈∪2 : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ' → (n , x) ∈ (Γ ∪ Γ')
  -- x∈∪2 Γ Γ' n x xin with Γ' n | Γ n
  -- x∈∪2 Γ Γ' n x₂ xin | Some x | Some x₁ = {!!}
  -- x∈∪2 Γ Γ' n x refl | Some .x | None = {!!}
  -- x∈∪2 Γ Γ' n x₁ xin | None   | _ = abort (somenotnone (! xin))

  x∈■ : {A : Set} (n : Nat) (a : A) → (n , a) ∈ (■ (n , a))
  x∈■ n a with natEQ n n
  x∈■ n a | Inl refl = refl
  x∈■ n a | Inr x = abort (x refl)

  -- x∈∪■ : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n , a) ∈ (Γ ∪ (■ (n , a)))
  -- x∈∪■ Γ n a with natEQ n n
  -- x∈∪■ Γ n a | Inl refl = {!!} -- it might be in Γ because i don't know that they're disjoint. this is where that premise gets you
  -- x∈∪■ Γ n a | Inr x = {!!}


  postulate -- TODO
    x∈sing : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n , a) ∈ (Γ ,, (n , a))
  -- x∈sing Γ n a  = {!!} -- x∈∪2 Γ (■ (n , a)) n a (x∈■ n a)
