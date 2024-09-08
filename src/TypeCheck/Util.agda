

module TypeCheck.Util where

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Agda.Builtin.Bool
open import Data.String using (String; _≟_; _++_ )

open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Reflects

open import Data.Sum.Base public using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product  public using (_×_ ; _,_; ∃)
open import Data.List     public using (List; []; _∷_; map)
open import Data.Maybe    public using (Maybe; just; nothing)

open import Data.List.Relation.Unary.Any using (Any); open Any

open import TypeCheck.Monad
open import Javalette.AST renaming (Expr to Exp; Ident to Id) hiding (String)
open import TypedSyntax using (_∈_; _∈'_; _∉_; Eq; Ord; Num; NonVoid; Basic; TypeTab; A)
open Eq; open Ord; open Num; open NonVoid; open Basic
open import WellTyped


InList : List (Id × A) → Id → Set
InList γ x = ∃ λ a → (x , a) ∈ γ

InScope : List (List (Id × A)) → Id → Set
InScope Γ x = ∃ λ t → (x , t) ∈' Γ

data InTypeTab (χ : TypeTab) (c : Id) : Set where
  inList : (n : Id) → (fs : List (Id × Type)) → (n , c , fs) ∈ χ → InTypeTab χ c

showId : Id → String
showId (ident s) = s

_eqId_  : (x y : Id) → (x ≢ y) ⊎ (x ≡ y)
_eqId_  (ident x) (ident y) with x ≟ y
... | .true  because ofʸ refl = inj₂ refl
... | .false because ofⁿ p    = inj₁ (λ {refl → p refl})

lookup : (x : Id) → (xs : List (Id × A)) → Maybe (InList xs x)
lookup id [] = nothing
lookup id ((x' , a) ∷ xs) with x' eqId id
... | inj₂ refl  = just (a , here refl)
... | inj₁ _ with lookup id xs
...         | just (t , x₁) = just (t , there x₁)
...         | nothing            = nothing

lookupTCM : (x : Id) → (xs : List (Id × A)) → TCM (InList xs x)
lookupTCM x xs with lookup x xs
... | just p = pure p
... | nothing = error ("lookup failed: " ++ showId x ++ " was not found")


lookupConstructor : (c : Id) → (xs : TypeTab) → TCM (InTypeTab xs c)
lookupConstructor x [] = error (("Struct " ++ showId x ++ " has no type"))
lookupConstructor x ((n , c , fs) ∷ xss) with x eqId c
... | inj₁ z = do inList n' fs' p ← lookupConstructor x xss
                  pure (inList n' fs' (there p))
... | inj₂ refl = pure (inList n fs (here refl))

lookupCtx : (x : Id) → (Γ : Ctx) → TCM (InScope Γ x)
lookupCtx x []   = error ("Var " ++ showId x ++ " is not in scope")
lookupCtx x (xs ∷ xss) with lookup x xs
... | just (t , x₁) = pure (t , here x₁)
... | nothing            = do t , p ← lookupCtx x xss
                              pure (t , there p)


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
ifEq (structT n)  = pure EqStruct
ifEq void       = error "Void is not Eq type"
ifEq (fun T ts) = error "Function is not Eq type"

ifOrd : (T : Type) → TCM (Ord T)
ifOrd bool       = error "Bool is not Ord type"
ifOrd int        = pure OrdInt
ifOrd doub       = pure OrdDouble
ifOrd (array _)  = error "Array is not Ord type"
ifOrd void       = error "Void is not Ord type"
ifOrd (structT _)  = error "Struct is not Ord type"
ifOrd (fun T ts) = error "Function is not Ord type"

ifNum : (T : Type) → TCM (Num T)
ifNum bool       = error "Bool is not nmeric"
ifNum int        = pure NumInt
ifNum doub       = pure NumDouble
ifNum (array _)  = error "Array is not Num type"
ifNum void       = error "Void is not numeric"
ifNum (structT _)  = error "Struct is not Num type"
ifNum (fun T ts) = error "Function is not Num type"

ifNonVoid : (χ : TypeTab) → (T : Type) → TCM (NonVoid χ T)
ifNonVoid χ bool       = pure NonVoidBool
ifNonVoid χ int        = pure NonVoidInt
ifNonVoid χ doub       = pure NonVoidDoub
ifNonVoid χ (array t)  = NonVoidArray <$> ifNonVoid χ t
ifNonVoid χ (structT n) = do _ , p ← lookupTCM n χ
                             pure (NonVoidStruct p)
ifNonVoid χ void       = error "Void is not-nonVoid"
ifNonVoid χ (fun T ts) = error "Function is not-nonVoid"

ifBasic : (χ : TypeTab) → (T : Type) → TCM (Basic χ T)
ifBasic χ bool       = pure BasicBool
ifBasic χ int        = pure BasicInt
ifBasic χ doub       = pure BasicDoub
ifBasic χ (array _)  = error "Array is not a Basic Type"
ifBasic χ (structT n)  = do _ , p ← lookupTCM n χ
                            pure (BasicStruct p)
ifBasic χ void       = error "Void is not a Basic Type"
ifBasic χ (fun T ts) = error "Function is not a Basic Type"


_=T=_ : (a b : Type) → (a ≡ b ⊎ a ≢ b) -- ⊎
eqLists' : (as : List Type) → (bs : List Type) → (as ≡ bs ⊎ as ≢ bs)
int  =T= int  = inj₁ refl
int  =T= doub = inj₂ (λ ())
int  =T= bool = inj₂ (λ ())
int  =T= void = inj₂ (λ ())
int  =T= (array _) = inj₂ (λ ())
int  =T= (structT _) = inj₂ (λ ())
int  =T= fun b ts = inj₂ (λ ())
doub =T= int = inj₂ (λ ())
doub =T= doub = inj₁ refl
doub =T= bool = inj₂ (λ ())
doub =T= void = inj₂ (λ ())
doub =T= (array _) = inj₂ (λ ())
doub =T= (structT _) = inj₂ (λ ())
doub =T= fun b ts = inj₂ (λ ())
bool =T= int = inj₂ (λ ())
bool =T= doub = inj₂ (λ ())
bool =T= bool = inj₁ refl
bool =T= void = inj₂ (λ ())
bool =T= (array _) = inj₂ (λ ())
bool =T= (structT _) = inj₂ (λ ())
bool =T= fun b ts = inj₂ (λ ())
void =T= int = inj₂ (λ ())
void =T= doub = inj₂ (λ ())
void =T= bool = inj₂ (λ ())
void =T= void = inj₁ refl
void =T= (array _) = inj₂ λ ()
void =T= (structT _) = inj₂ (λ ())
void =T= fun b ts = inj₂ (λ ())
structT x =T= int  = inj₂ (λ ())
structT x =T= doub = inj₂ (λ ())
structT x =T= bool = inj₂ (λ ())
structT x =T= void = inj₂ (λ ())
structT x =T= fun y ts = inj₂ (λ ())
structT x =T= array y = inj₂ (λ ())
structT x =T= structT x₁ with x eqId x₁
... | inj₁ x₂ = inj₂ λ {refl → x₂ refl}
... | inj₂ refl = inj₁ refl
array x =T= int  = inj₂ (λ ())
array x =T= doub = inj₂ (λ ())
array x =T= bool = inj₂ (λ ())
array x =T= void = inj₂ (λ ())
array x =T= (structT _) = inj₂ (λ ())
array x =T= fun y ts = inj₂ (λ ())
array x =T= array y with x =T= y
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ (λ {refl → p refl})
fun a ts =T= int = inj₂ (λ ())
fun a ts =T= doub = inj₂ (λ ())
fun a ts =T= bool = inj₂ (λ ())
fun a ts =T= void = inj₂ (λ ())
fun a ts =T= (array _) = inj₂ (λ ())
fun a ts =T= (structT _) = inj₂ (λ ())
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
