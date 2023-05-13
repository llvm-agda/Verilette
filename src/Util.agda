

module Util where

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Agda.Builtin.Bool
open import Data.String using (String; _≟_; _++_ )

open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Reflects

open import Data.Sum.Base public using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product  public using (_×_ ; _,_)
open import Data.List     public using (List; []; _∷_)
open import Data.Maybe    public using (Maybe; just; nothing)

open import Data.List.Relation.Unary.Any using (Any); open Any

open import TypeCheckerMonad
open import Javalette.AST renaming (Expr to Exp; Ident to Id) hiding (String)
open import TypedSyntax Id


data InList {A : Set} (γ : List (Id × A)) (x : Id) : Set where
  inList : (t : A) → (x , t) ∈ γ → InList γ x

showId : Id → String
showId (ident s) = s

_eqId_  : (x y : Id) → (x ≢ y) ⊎ (x ≡ y)
_eqId_  (ident x) (ident y) with x ≟ y
... | .true  because ofʸ refl = inj₂ refl
... | .false because ofⁿ p    = inj₁ (λ {refl → p refl})

data InScope (Γ : Ctx) (x : Id) : Set where
  inScope : (t : Type) → (x , t) ∈' Γ → InScope Γ x

lookup : (x : Id) → (xs : List (Id × A)) → Maybe (InList xs x)
lookup id [] = nothing
lookup id ((x' , a) ∷ xs) with x' eqId id
... | inj₂ refl  = just (inList a (here refl))
... | inj₁ _ with lookup id xs
...         | just (inList t x₁) = just (inList t (there x₁))
...         | nothing            = nothing

lookupTCM : (x : Id) → (xs : List (Id × A)) → TCM (InList xs x)
lookupTCM x xs with lookup x xs
... | just p = pure p
... | nothing = error ("lookup failed: " ++ showId x ++ " was not found")


lookupCtx : (x : Id) → (Γ : Ctx) → TCM (InScope Γ x)
lookupCtx x []   = error ("Var " ++ showId x ++ " is not in scope")
lookupCtx x (xs ∷ xss) with lookup x xs
... | just (inList t x₁) = pure (inScope t (here x₁))
... | nothing            = do inScope t p ← lookupCtx x xss
                              pure (inScope t (there p))


checkAll : {P : A → Set} → ((a : A) → TCM (P a)) → (as : List A) → TCM (All P as)
checkAll P []       = pure []
checkAll P (x ∷ xs) = _∷_ <$> P x <*> checkAll P xs


_notIn_ : (x : Id) → (xs : List (Id × A)) → TCM (x ∉ xs)
id notIn xs = checkAll (λ (id' , _) → notEq id id') xs
  where notEq : (x y : Id) → TCM (x ≢ y)
        notEq id id' with id eqId id'
        ... | inj₁ x = pure x
        ... | inj₂ y = error (showId id ++ " was already in scope when delcaring new var")


ifEq : (T : Type) → TCM (Eq T)
ifEq bool       = pure EqBool
ifEq int        = pure EqInt
ifEq doub       = pure EqDouble
ifEq (array _)  = error "Array is not Eq type"
ifEq void       = error "Void is not Eq type"
ifEq (fun T ts) = error "Function is not Eq type"

ifOrd : (T : Type) → TCM (Ord T)
ifOrd bool       = error "Bool is not Ord type"
ifOrd int        = pure OrdInt
ifOrd doub       = pure OrdDouble
ifOrd (array _)  = error "Array is not Ord type"
ifOrd void       = error "Void is not Ord type"
ifOrd (fun T ts) = error "Function is not Ord type"

ifNum : (T : Type) → TCM (Num T)
ifNum bool       = error "Bool is not nmeric"
ifNum int        = pure NumInt
ifNum doub       = pure NumDouble
ifNum (array _)  = error "Array is not Num type"
ifNum void       = error "Void is not numeric"
ifNum (fun T ts) = error "Function is not Num type"

ifNonVoid : (T : Type) → TCM (NonVoid T)
ifNonVoid bool       = pure NonVoidBool
ifNonVoid int        = pure NonVoidInt
ifNonVoid doub       = pure NonVoidDoub
ifNonVoid (array t)  = NonVoidArray <$> ifNonVoid t
ifNonVoid void       = error "Void is not-nonVoid"
ifNonVoid (fun T ts) = error "Function is not-nonVoid"

ifBasic : (T : Type) → TCM (Basic T)
ifBasic bool       = pure BasicBool
ifBasic int        = pure BasicInt
ifBasic doub       = pure BasicDoub
ifBasic (array _)  = error "Array is not Eq type"
ifBasic void       = error "Void is not Eq type"
ifBasic (fun T ts) = error "Function is not Eq type"


_=T=_ : (a b : Type) → (a ≡ b ⊎ a ≢ b) -- ⊎
eqLists' : (as : List Type) → (bs : List Type) → (as ≡ bs ⊎ as ≢ bs)
int  =T= int  = inj₁ refl
int  =T= doub = inj₂ (λ ())
int  =T= bool = inj₂ (λ ())
int  =T= void = inj₂ (λ ())
int  =T= (array _) = inj₂ (λ ())
int  =T= fun b ts = inj₂ (λ ())
doub =T= int = inj₂ (λ ())
doub =T= doub = inj₁ refl
doub =T= bool = inj₂ (λ ())
doub =T= void = inj₂ (λ ())
doub =T= (array _) = inj₂ (λ ())
doub =T= fun b ts = inj₂ (λ ())
bool =T= int = inj₂ (λ ())
bool =T= doub = inj₂ (λ ())
bool =T= bool = inj₁ refl
bool =T= void = inj₂ (λ ())
bool =T= (array _) = inj₂ (λ ())
bool =T= fun b ts = inj₂ (λ ())
void =T= int = inj₂ (λ ())
void =T= doub = inj₂ (λ ())
void =T= bool = inj₂ (λ ())
void =T= void = inj₁ refl
void =T= (array _) = inj₂ λ ()
void =T= fun b ts = inj₂ (λ ())
array x =T= int  = inj₂ (λ ())
array x =T= doub = inj₂ (λ ())
array x =T= bool = inj₂ (λ ())
array x =T= void = inj₂ (λ ())
array x =T= fun y ts = inj₂ (λ ())
array x =T= array y with x =T= y
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ (λ {refl → p refl})
fun a ts =T= int = inj₂ (λ ())
fun a ts =T= doub = inj₂ (λ ())
fun a ts =T= bool = inj₂ (λ ())
fun a ts =T= void = inj₂ (λ ())
fun a ts =T= (array _) = inj₂ (λ ())
fun a as =T= fun b bs with eqLists' (a ∷ as) (b ∷ bs)
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ λ {refl → p refl}

eqLists' []       []       = inj₁ refl
eqLists' (a ∷ as) (b ∷ bs) with a =T= b
... | inj₂ p = inj₂ λ {refl → p refl}
... | inj₁ refl with eqLists' as bs
... |    inj₁ refl = inj₁ refl
... |    inj₂ p    = inj₂ (λ {refl → p refl})
eqLists' [] (b ∷ bs) = inj₂ (λ ()) 
eqLists' (a ∷ as) [] = inj₂ (λ ()) 

_=?=_ : (a b : Type) → TCM (a ≡ b)
a =?= b with a =T= b
... | inj₁ x = pure x
... | inj₂ y = error "Type mismatch"

_=/=_ : (a b : Type) → TCM (a ≢ b)
a =/= b with a =T= b
... | inj₁ y = error "Type mismatch"
... | inj₂ x = pure x


eqLists  : (as : List Type) → (bs : List Type) → TCM (as ≡ bs)
eqLists as bs with eqLists' as bs
... | inj₁ x = pure x
... | inj₂ y = error "Type mismatch when comparing lists"
