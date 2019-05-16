# | ~C-x C-a~ | transform org ~org-agda~ blocks to literate Agda blocs        |
# | ~C-x C-o~ | transform literate Agda code delimiters to org ~org-agda~ src |
#
# Need to ensure org-indent-mode is off when going to agda.

#
#+TITLE: A Gentle Introduction to Reflection in Agda
#+DESCRIPTION: How can we use a single proof to prove two different theorems? One proof pattern, multiple invocations!
#+AUTHOR: Musa Al-hassy
#+EMAIL: alhassy@gmail.com
#+STARTUP: indent
#+PROPERTY: header-args :tangle tangled.agda :comments links

#+CATEGORIES: Agda Org Emacs
#+OPTIONS: html-postamble:nil toc:nil d:nil tag:nil
#+IMAGE: ../assets/img/org_logo.png
#+SOURCE: https://raw.githubusercontent.com/alhassy/org-agda-mode/master/literate.lagda

# INCLUDE: ~/Dropbox/MyUnicodeSymbols.org

* Abstract       :ignore:
#+BEGIN_CENTER org
*Abstract*
#+END_CENTER

/One proof for two different theorems!/

Let's learn how we can do that in Agda.

This tutorial is the result of mostly experimenting with the
[[https://agda.readthedocs.io/en/v2.5.2/language/reflection.html][documentation]] on Agda's reflection mechanism, which essentially
only exposes the reflection interface and provides a few tiny examples.
The goal of this tutorial is to contain a diverse variety of examples,
along with occasional exercises for the reader.

Examples include:
+ String manipulation of built-in identifier names. 🍓
+ Handy dandy combinators for AST formation: ~𝓋𝓇𝒶, λ𝓋_↦_, …~. 🛠
+ Numerous examples of quotation of terms and types. 🎯
+ Wholesale derivation of singleton types for an example datatype,
  along with derivable proofs 💛 🎵
+ Automating proofs that are only ~refl~ /with/ pattern matching 🏄
+ Discussion of C-style macros in Agda 🌵
+ Abstracting proofs patterns without syntactic overhead using macros 💪 🎼
+ Remarks on what I could not do, possibly since it cannot be done :sob:

Everything here works with Agda version 2.6.0.
#+TOC: headlines 2

* Imports

#+BEGIN_SRC org-agda
module gentle-intro-to-reflection where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Reflection hiding (_≟_ ; name)
open import Data.List as List
open import Relation.Nullary

open import Reflection

open import Data.Nat
open import Data.Bool
open import Data.String as String

open import Data.Unit

import Level as Level

open import Data.Char as Char
open import Relation.Unary using (Decidable)

open import Data.Product

open import Relation.Nullary
#+END_SRC

* Intro

/Reflection/ is the ability to convert program code into an abstract syntax,
a data structure that can be manipulated like any other.

Consider, for example, the tedium of writing a decidable equality for an enumerated type.
Besides being tedious and error-prone, the inexpressibility of
what should be a mechanically-derivable concept
obscures the corresponding general principle underlying it, thus foregoing
any machine assistance in ensuring any correctness or safety-ness guarantees.
Reflection allows a more economical and disciplined approach.

It is the aim of this tutorial to show how to get started with reflection in Agda.
To the best of my knowledge there is no up to date tutorial on this matter.


There are three main types in Agda's reflection mechanism:
~Name, Arg, Term~.


#+BEGIN_SRC org-agda
data RGB : Set where
  Red Green Blue : RGB
#+END_SRC
* ~NAME~ ─Type of known identifiers                         :forward_todo_link:

~Name~ is the type of quoting identifiers, Agda names.
Elements of this type can be formed and pattern matched using
the ~quote~ keyword.

#+BEGIN_SRC org-agda
a-name : Name
a-name = quote ℕ

isNat : Name → Bool
isNat (quote ℕ) = true
isNat _         = false

-- bad : Set → Name
-- bad s = quote s  {- s is not known -}
#+END_SRC

+ ~NAME~ comes equipped with equality, ordering, and a show function.
+ Quote will not work on function arguments; the identifier must be known.

Let's show names:
#+BEGIN_SRC org-agda
_ : showName (quote _≡_) ≡ "Agda.Builtin.Equality._≡_"
_ = refl

_ : showName (quote Red) ≡ "gentle-intro-to-reflection.RGB.Red"
_ = refl
#+END_SRC

It would be nice to have ~Red~ be shown as just ~“RGB.Red”~.

First, let's introduce some ‘programming’ helpers to treat Agda strings as if they
where Haskell strings, and likewise to treat predicates as decidables.
#+BEGIN_SRC org-agda
{- Like “$” but for strings. -}
_⟨𝒮⟩_ : (List Char → List Char) → String → String
f ⟨𝒮⟩ s = fromList (f (toList s))

{- This should be in the standard library; I could not locate it. -}
toDec : ∀ {ℓ} {A : Set ℓ} → (p : A → Bool) → Decidable {ℓ} {A} (λ a → p a ≡ true)
toDec p x with p x
toDec p x | false = no λ ()
toDec p x | true = yes refl
#+END_SRC

We can now easily obtain the module's name, then drop it from the data constructor's name.
#+BEGIN_SRC org-agda
module-name : String
module-name = takeWhile (toDec (λ c → not (c Char.== '.'))) ⟨𝒮⟩ showName (quote Red)

_ : module-name ≡ "gentle-intro-to-reflection"
_ = refl

strName : Name → String
strName n = drop (1 + String.length module-name) ⟨𝒮⟩ showName n
{- The “1 +” is for the “.” seperator in qualified names. -}

_ : strName (quote Red) ≡ "RGB.Red"
_ = refl
#+END_SRC

~NAME~ essentially provides us with the internal representation of a known name,
for which we can query to obtain its definition or type.
Later we will show how to get the type constructors of ~ℕ~ from its name.

* ~Arg~ ─Type of arguments

Arguments in Agda may be hidden or computationally irrelevant.
This information is captured by the ~Arg~ type.

#+BEGIN_EXAMPLE org-agda
{- Arguments can be (visible), {hidden}, or ⦃instance⦄ -}
data Visibility : Set where
  visible hidden instance′ : Visibility

{-Arguments can be relevant or irrelevant: -}
data Relevance : Set where
  relevant irrelevant : Relevance

{- Visibility and relevance characterise the behaviour of an argument: -}
data ArgInfo : Set where
  arg-info : (v : Visibility) (r : Relevance) → ArgInfo

data Arg (A : Set) : Set where
  arg : (i : ArgInfo) (x : A) → Arg A
#+END_EXAMPLE

For example, let's create some helpers that make arguments of any given type ~A~:
#+BEGIN_SRC org-agda
variable {A} : Set

{- 𝓋isible 𝓇elevant 𝒶rgument -}
𝓋𝓇𝒶 : A → Arg A
𝓋𝓇𝒶 = arg (arg-info visible relevant)

{- 𝒽idden 𝓇elevant 𝒶rgument -}
𝒽𝓇𝒶 : A → Arg A
𝒽𝓇𝒶 = arg (arg-info hidden relevant)
#+END_SRC

Below are the variable counterparts, for the ~Term~ datatype,
which will be discussed shortly.
+ Variables are De Bruijn indexed and may be applied to a list of arguments.
+ The index /n/ refers to the argument that is /n/ locations away from ‘here’.

#+BEGIN_SRC org-agda
{- 𝓋isible 𝓇elevant 𝓋ariable -}
𝓋𝓇𝓋 : (debruijn : ℕ) (args : List (Arg Term)) → Arg Term
𝓋𝓇𝓋 n args = arg (arg-info visible relevant) (var n args)

{- 𝒽idden 𝓇elevant 𝓋ariable -}
𝒽𝓇𝓋 : (debruijn : ℕ) (args : List (Arg Term)) → Arg Term
𝒽𝓇𝓋 n args = arg (arg-info hidden relevant) (var n args)
#+END_SRC

* ~Term~ ─Type of terms

We use the ~quoteTerm~ keyword to turn a well-typed fragment of code
---concrete syntax--- into a value of the ~Term~ datatype ---the abstract syntax.
Here's the definition of ~Term~:
#+BEGIN_EXAMPLE org-agda
data Term where

  {- A variable has a De Bruijn index and may be applied to arguments. -}
  var       : (x : ℕ)  (args : List (Arg Term)) → Term

  {- Constructors and definitions may be applied to a list of arguments. -}
  con       : (c : Name) (args : List (Arg Term)) → Term
  def       : (f : Name) (args : List (Arg Term)) → Term

  {- λ-abstractions bind one varaible; “t” is the string name of the variable
    along with the body of the lambda.
  -}
  lam       : (v : Visibility) (t : Abs Term) → Term  {- Abs A  ≅  String × A -}
  pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term

  {- Telescopes, or function types; λ-abstraction for types. -}
  pi        : (a : Arg Type) (b : Abs Type) → Term

  {- “Set n” or some term that denotes a type -}
  agda-sort : (s : Sort) → Term

  {- Metavariables; introduced via quoteTerm -}
  meta      : (x : Meta) → List (Arg Term) → Term

  {- Literal  ≅  ℕ | Word64 | Float | Char | String | Name | Meta -}
  lit       : (l : Literal) → Term

  {- Items not representable by this AST; e.g., a hole. -}
  unknown   : Term {- Treated as '_' when unquoting. -}

data Sort where
  set     : (t : Term) → Sort {- A Set of a given (possibly neutral) level. -}
  lit     : (n : Nat) → Sort  {- A Set of a given concrete level. -}
  unknown : Sort

data Clause where
  clause        : (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (ps : List (Arg Pattern)) → Clause
#+END_EXAMPLE

** Example: Simple Types

Here are three examples of “def”ined names, the first two do not take an argument.
The last takes a visible and relevant argument, 𝓋𝓇𝒶, that is a literal natural.
#+BEGIN_SRC org-agda
import Data.Vec as V
import Data.Fin as F

_ : quoteTerm ℕ ≡ def (quote ℕ) []
_ = refl

_ : quoteTerm V.Vec ≡ def (quote V.Vec) []
_ = refl

_ : quoteTerm (F.Fin 3) ≡ def (quote F.Fin) (𝓋𝓇𝒶 (lit (nat 3)) ∷ [])
_ = refl
#+END_SRC

** Example: Simple Terms

Elementary numeric quotations:
#+BEGIN_SRC org-agda
_ : quoteTerm 1 ≡ lit (nat 1)
_ = refl

_ :    quoteTerm (suc zero)
     ≡ con (quote suc) (arg (arg-info visible relevant) (quoteTerm zero) ∷ [])
_ = refl

{- Using our helper 𝓋𝓇𝒶 -}
_ : quoteTerm (suc zero) ≡ con (quote suc) (𝓋𝓇𝒶 (quoteTerm zero) ∷ [])
_ = refl
#+END_SRC

The first example below demonstrates that ~true~ is a type “con”structor
that takes no arguments, whence the ~[]~. The second example shows that
~_≡_~ is a defined name, not currently applied to any arguments.
The final example has propositional equality applied to two arguments.
#+BEGIN_SRC org-agda
_ : quoteTerm true ≡ con (quote true) []
_ = refl

_ : quoteTerm _≡_ ≡ def (quote _≡_) []
_ = refl

_ :   quoteTerm ("b" ≡ "a")
    ≡ def (quote _≡_)
      ( 𝒽𝓇𝒶 (def (quote Level.zero) [])
      ∷ 𝒽𝓇𝒶 (def (quote String) [])
      ∷ 𝓋𝓇𝒶 (lit (string "b"))
      ∷ 𝓋𝓇𝒶 (lit (string "a")) ∷ [])
_ = refl
#+END_SRC

Notice that a propositional equality actually has four arguments ─a level, a type, and two arguments─
where the former two happen
to be inferrable from the latter.
Here is a more polymorphic example:
#+BEGIN_SRC org-agda
_ : ∀ {level : Level.Level}{Type : Set level} (x y : Type)
    →   quoteTerm (x ≡ y)
       ≡ def (quote _≡_)
           (𝒽𝓇𝓋 3 [] ∷ 𝒽𝓇𝓋 2 [] ∷ 𝓋𝓇𝓋 1 [] ∷ 𝓋𝓇𝓋 0 [] ∷ [])

_ = λ x y → refl
#+END_SRC

We will demonstrate an example of a section, say
~≡_ "b"~, below when discussing lambda abstractions.

** A relationship between ~quote~ and ~quoteTerm~

Known names ~f'~ in a quoted term are denoted by a ~quote f'~ in the AST representation.
#+BEGIN_SRC org-agda
postulate A' B' : Set
postulate f' : A' → B'
_ : quoteTerm f' ≡ def (quote f') []
_ = refl
#+END_SRC

In contrast, names that /vary/ are denoted by a ~var~ constructor in the AST representation.
#+BEGIN_SRC org-agda
module _ {A B : Set} {f : A → B} where
  _ : quoteTerm f ≡ var 0 []
  _ = refl
#+END_SRC

** Example: Lambda Terms

First we show how reductions with lambdas works then we show how lambda functions
are represented as ~Term~ values.

~quoteTerm~ typechecks and normalises its argument before yielding a ~Term~ value.
#+BEGIN_SRC org-agda
_ : quoteTerm ((λ x → x) "nice") ≡ lit (string "nice")
_ = refl
#+END_SRC

Eta-reduction happens, ~f ≈ λ x → f x~.
#+BEGIN_SRC org-agda
id : {A : Set} → A → A
id x = x

_ :   quoteTerm (λ (x : ℕ) → id x)
    ≡ def (quote id) (𝒽𝓇𝒶 (def (quote ℕ) []) ∷ [])
_ = refl
#+END_SRC

No delta-reduction happens; function definitions are not elaborated.
#+BEGIN_SRC org-agda
_ :   quoteTerm (id "a")
    ≡ def (quote id)
        (𝒽𝓇𝒶 (def (quote String) []) ∷  𝓋𝓇𝒶 (lit (string "a")) ∷ [])
_ = refl
#+END_SRC

Here is a simple identity function on the Booleans.
A “lam”da with a “visible” “abs”tract argument named ~"x"~ is introduced
having as body merely being the 0 nearest-bound variable, applied to an empty
list of arguments.
#+BEGIN_SRC org-agda
_ : quoteTerm (λ (x : Bool) → x) ≡ lam visible (abs "x" (var 0 []))
_ = refl

#+END_SRC

Here is a more complicated lambda abstraction: Note that ~f a~ is represented as
the variable 0 lambdas away from the body applied to the variable 1 lambda away
from the body.
#+BEGIN_SRC org-agda
_ : quoteTerm (λ (a : ℕ) (f : ℕ → ℕ) → f a)
    ≡  lam visible (abs "a"
         (lam visible (abs "f"
           (var 0 (arg (arg-info visible relevant) (var 1 []) ∷ [])))))
_ = refl
#+END_SRC

This is rather messy, let's introduce some syntactic sugar to make it more readable.
#+BEGIN_SRC org-agda
infixr 5 λ𝓋_↦_  λ𝒽_↦_

λ𝓋_↦_  λ𝒽_↦_ : String → Term → Term
λ𝓋 x ↦ body  = lam visible (abs x body)
λ𝒽 x ↦ body  = lam hidden (abs x body)
#+END_SRC
Now the previous example is a bit easier on the eyes:
#+BEGIN_SRC org-agda
_ :   quoteTerm (λ (a : ℕ) (f : ℕ → ℕ) → f a)
    ≡ λ𝓋 "a" ↦ λ𝓋 "f" ↦ var 0 [ 𝓋𝓇𝒶 (var 1 []) ]
_ = refl
#+END_SRC

Using that delicious sugar, let's look at the constant function a number of ways.
#+BEGIN_SRC org-agda
_ : {A B : Set} →   quoteTerm (λ (a : A) (b : B) → a)
                  ≡ λ𝓋 "a" ↦ (λ𝓋 "b" ↦ var 1 [])
_ = refl

_ :  quoteTerm (λ {A B : Set} (a : A) (_ : B) → a)
    ≡ (λ𝒽 "A" ↦ (λ𝒽 "B" ↦ (λ𝓋 "a" ↦ (λ𝓋 "_" ↦ var 1 []))))
_ = refl

const : {A B : Set} → A → B → A
const a _ = a

_ : quoteTerm const ≡ def (quote const) []
_ = refl
#+END_SRC

Finally, here's an example of a section.
#+BEGIN_SRC org-agda
_ :   quoteTerm (_≡ "b")
    ≡ λ𝓋 "section" ↦
       (def (quote _≡_)
        (𝒽𝓇𝒶 (def (quote Level.zero) []) ∷
         𝒽𝓇𝒶(def (quote String) []) ∷
         𝓋𝓇𝒶 (var 0 []) ∷
         𝓋𝓇𝒶 (lit (string "b")) ∷ []))
_ = refl
#+END_SRC

* Metaprogramming with The Typechecking Monad ~TC~
The ~TC~ monad provides an interface to Agda's type checker.
#+BEGIN_EXAMPLE org-agda
postulate
  TC       : ∀ {a} → Set a → Set a
  returnTC : ∀ {a} {A : Set a} → A → TC A
  bindTC   : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
#+END_EXAMPLE

In order to use ~do~-notation we need to have the following definitions in scope.
#+BEGIN_SRC org-agda
_>>=_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
_>>_  = λ p q → p >>= (λ _ → q)
#+END_SRC

The primitives of ~TC~ can be seen on the [[https://agda.readthedocs.io/en/v2.6.0/language/reflection.html#type-checking-computations][documentation]] page; below are a few notable
ones that we may use. Other primitives include support for the current context,
type errors, and metavariables.
#+BEGIN_EXAMPLE org-agda
postulate
  {- Take what you have and try to make it fit into the current goal. -}
  unify : (have : Term) (goal : Term) → TC ⊤

  {- Try first computation, if it crashes with a type error, try the second. -}
  catchTC : ∀ {a} {A : Set a} → TC A → TC A → TC A

  {- Infer the type of a given term. -}
  inferType : Term → TC Type

  {- Check a term against a given type. This may resolve implicit arguments
     in the term, so a new refined term is returned. Can be used to create
     new metavariables: newMeta t = checkType unknown t -}
  checkType : Term → Type → TC Term

  {- Compute the normal form of a term. -}
  normalise : Term → TC Term

  {- Quote a value, returning the corresponding Term. -}
  quoteTC : ∀ {a} {A : Set a} → A → TC Term

  {- Unquote a Term, returning the corresponding value. -}
  unquoteTC : ∀ {a} {A : Set a} → Term → TC A

  {- Create a fresh name. -}
  freshName : String → TC Name

  {- Declare a new function of the given type. The function must be defined
     later using 'defineFun'. Takes an Arg Name to allow declaring instances
     and irrelevant functions. The Visibility of the Arg must not be hidden. -}
  declareDef : Arg Name → Type → TC ⊤

  {- Define a declared function. The function may have been declared using
     'declareDef' or with an explicit type signature in the program. -}
  defineFun : Name → List Clause → TC ⊤

  {- Get the type of a defined name. Replaces 'primNameType'. -}
  getType : Name → TC Type

  {- Get the definition of a defined name. Replaces 'primNameDefinition'. -}
  getDefinition : Name → TC Definition

  {-  Change the behaviour of inferType, checkType, quoteTC, getContext
      to normalise (or not) their results. The default behaviour is no
      normalisation. -}
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A
#+END_EXAMPLE

~TC~ computations, or “metaprograms”, can be run by declaring them as macros or by
unquoting. Let's begin with the former.

* Unquoting ─Making new functions & types

Recall our ~RGB~ example type was a simple enumeration consisting of ~Red, Green, Blue~.
Consider the singleton type:
#+BEGIN_EXAMPLE org-agda
data IsRed : RGB → Set where
  yes : IsRed Red
#+END_EXAMPLE
The name ~Red~ completely determines this datatype; so let's try to generate it
mechanically. Unfortunately, as far as I could tell, there is currently no way
to unquote ~data~ declarations. As such, we'll settle for the following
isomorphic functional formulation:
#+BEGIN_EXAMPLE org-agda
IsRed : RGB → Set
IsRed x = x ≡ Red
#+END_EXAMPLE

First, let's quote the relevant parts, for readability.
#+BEGIN_SRC org-agda
“ℓ₀” : Arg Term
“ℓ₀” = 𝒽𝓇𝒶 (def (quote Level.zero) [])

“RGB” : Arg Term
“RGB” = 𝒽𝓇𝒶 (def (quote RGB) [])

“Red” : Arg Term
“Red” = 𝓋𝓇𝒶 (con (quote Red) [])
#+END_SRC
The first two have a nearly identical definition and it would be nice to
mechanically derive them...

Anyhow,
we use the ~unquoteDecl~ keyword, which allows us to obtain a ~NAME~ value, ~IsRed~.
We then quote the desired type, declare a function of that type, then define it
using the provided ~NAME~.
#+BEGIN_SRC org-agda
unquoteDecl IsRed =
  do ty ← quoteTC (RGB → Set)
     declareDef (𝓋𝓇𝒶 IsRed) ty
     defineFun IsRed   [ clause [ 𝓋𝓇𝒶 (var "x") ] (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ “Red” ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]
#+END_SRC
Let's try out our newly declared type.
#+BEGIN_SRC org-agda
red-is-a-solution : IsRed Red
red-is-a-solution = refl

green-is-not-a-solution : ¬ (IsRed Green)
green-is-not-a-solution = λ ()

red-is-the-only-solution : ∀ {c} → IsRed c → c ≡ Red
red-is-the-only-solution refl = refl
#+END_SRC

There is a major problem with using ~unquoteDef~ outright like this:
We cannot step-wise refine our program using holes ~?~, since that would
result in unsolved meta-variables. Instead, we split this process into two stages:
A programming stage, then an unquotation stage.

#+BEGIN_SRC org-agda
{- Definition stage, we can use ‘?’ as we form this program. -}
define-Is : Name → Name → TC ⊤
define-Is is-name qcolour = defineFun is-name
  [ clause [ 𝓋𝓇𝒶 (var "x") ] (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ 𝓋𝓇𝒶 (con qcolour []) ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]

declare-Is : Name → Name → TC ⊤
declare-Is is-name qcolour =
  do let η = is-name
     τ ← quoteTC (RGB → Set)
     declareDef (𝓋𝓇𝒶 η) τ
     defineFun is-name
       [ clause [ 𝓋𝓇𝒶 (var "x") ]
         (def (quote _≡_) (“ℓ₀” ∷ “RGB” ∷ 𝓋𝓇𝒶 (con qcolour []) ∷ 𝓋𝓇𝓋 0 [] ∷ [])) ]

{- Unquotation stage -}
IsRed′ : RGB → Set
unquoteDef IsRed′ = define-Is IsRed′ (quote Red)

{- Trying it out -}
_ : IsRed′ Red
_ = refl
#+END_SRC

Notice that if we use “unquoteDef”, we must provide a type signature.
We only do so for illustration; the next code block avoids such a redundancy by
using “unquoteDecl”.

The above general approach lends itself nicely to the other data constructors as well:
#+BEGIN_SRC org-agda
unquoteDecl IsBlue  = declare-Is IsBlue  (quote Blue)
unquoteDecl IsGreen = declare-Is IsGreen (quote Green)

{- Example use -}
disjoint-rgb  : ∀{c} → ¬ (IsBlue c × IsGreen c)
disjoint-rgb (refl , ())
#+END_SRC

The next natural step is to avoid manually invoking ~declare-Is~ for each constructor.
Unfortunately, it seems fresh names are not accessible, for some reason. 😢

For example, you would think the following would produce a function
named ~gentle-intro-to-reflection.identity~. Yet, it is not in scope.
I even tried extracting the definition to its own file and no luck.
#+BEGIN_SRC org-agda
unquoteDecl {- identity -}
  = do {- let η = identity -}
       η ← freshName "identity"
       τ ← quoteTC (∀ {A : Set} → A → A)
       declareDef (𝓋𝓇𝒶 η) τ
       defineFun η [ clause [ 𝓋𝓇𝒶 (var "x") ] (var 0 []) ]

{- “identity” is not in scope!?
_ : ∀ {x : ℕ}  →  identity x  ≡  x
_ = refl
-}
#+END_SRC

*Exercises*:
0. Comment out the ~freshName~ line above and uncomment the surrounding artifacts to so that the above
   unit test goes through.
1. Using that as a template, unquote a function ~everywhere-0 : ℕ → ℕ~ that is constantly 0.
2. Unquote the constant combinator ~K : {A B : Set} → A → B → A~.
#+BEGIN_EXAMPLE org-agda
unquoteDecl everywhere-0
  = do ⋯

_ : everywhere-0 3 ≡ 0
_ = refl

unquoteDecl K
  = do ⋯

_ : K 3 "cat" ≡ 3
_ = refl
#+END_EXAMPLE

*Bonus:* Proofs of a singleton type such as ~IsRed~ are essentially the same for all singelton types
over ~RGB~. Write, in two stages, a metaprogram that demonstrates each singleton type has a single member
─c.f., ~red-is-the-only-solution~ from above. Hint: This question is as easy as the ones before it.
#+BEGIN_EXAMPLE org-agda
{- Programming stage }
declare-unique : Name → (RGB → Set) → RGB → TC ⊤
declare-unique it S colour =
  = do ⋯

{- Unquotation stage -}
unquoteDecl red-unique = declare-unique red-unique IsRed Red
unquoteDecl green-unique = declare-unique green-unique IsGreen Green
unquoteDecl blue-unique = declare-unique blue-unique IsBlue Blue

{- Test -}
_ : ∀ {c} → IsGreen c → c ≡ Green
_ = green-unique
#+END_EXAMPLE

:Solutions:
#+BEGIN_SRC org-agda
{- Exercise: -}
unquoteDecl everywhere-0
  = do let η = everywhere-0
       τ ← quoteTC (ℕ → ℕ)
       declareDef (𝓋𝓇𝒶 η) τ
       defineFun η [ clause [ 𝓋𝓇𝒶 (var "x") ] (con (quote zero) []) ]

_ : everywhere-0 3 ≡ 0
_ = refl
{- End -}

{- Exercise: -}
unquoteDecl K
  = do let η = K
       τ ← quoteTC ({A B : Set} → A → B → A)
       declareDef (𝓋𝓇𝒶 η) τ
       defineFun η [ clause (𝓋𝓇𝒶 (var "x") ∷ 𝓋𝓇𝒶 (var "y") ∷ []) (var 1 []) ]

_ : K 3 "cat" ≡ 3
_ = refl
{- End -}

{- Exercise: -}
declare-unique : Name → (RGB → Set) → RGB → TC ⊤
declare-unique it S colour =
  do let η = it
     τ ← quoteTC (∀ {c} → S c → c ≡ colour)
     declareDef (𝓋𝓇𝒶 η) τ
     defineFun η [ clause [ 𝓋𝓇𝒶 (con (quote refl) []) ] (con (quote refl) []) ]

unquoteDecl red-unique = declare-unique red-unique IsRed Red
unquoteDecl green-unique = declare-unique green-unique IsGreen Green
unquoteDecl blue-unique = declare-unique blue-unique IsBlue Blue

_ : ∀ {c} → IsGreen c → c ≡ Green
_ = green-unique
{- End -}
#+END_SRC
:End:

:Failed_exploration:
#+BEGIN_EXAMPLE org-agda
RGB-constructors : Definition → Name × Name × Name
RGB-constructors (data-type pars (x ∷ y ∷ z ∷ cs)) = x , y , z
RGB-constructors _ = n , n , n where n = quote RGB

unquoteDecl
  =    do δ ← getDefinition (quote RGB)

          let r , g , b = RGB-constructors δ
       -- TODO: get unqualified name, then prefix it with "Is",
       -- then make that into a new name. Then declare a function with that name.

          η ← freshName "IsX"
          -- let η = r
          τ ← quoteTC (RGB → Set)
          declareDef (𝓋𝓇𝒶 η) τ
          define-Is η

-- _ : {!!} -- IsX Red -- gentle-intro-to-reflection.IsX
-- _ = {!IsX!}
--
#+END_EXAMPLE
:End:

* Sidequest: Avoid tedious ~refl~ proofs

Time for a breather (•̀ᴗ•́)و

Look around your code base for a function that makes explicit pattern matching, such as:
#+BEGIN_SRC org-agda
just-Red : RGB → RGB
just-Red Red   = Red
just-Red Green = Red
just-Red Blue  = Red

only-Blue : RGB → RGB
only-Blue Blue = Blue
only-Blue _   = Blue
#+END_SRC

Such functions have properties which cannot be proven unless we pattern match
on the arguments they pattern match. For example, that the above function is
constantly ~Red~ requires pattern matching then a ~refl~ for each clause.
#+BEGIN_SRC org-agda
just-Red-is-constant : ∀{c} → just-Red c ≡ Red
just-Red-is-constant {Red}   = refl
just-Red-is-constant {Green} = refl
just-Red-is-constant {Blue}  = refl

{- Yuck, another tedious proof -}
only-Blue-is-constant : ∀{c} → only-Blue c ≡ Blue
only-Blue-is-constant {Blue}  = refl
only-Blue-is-constant {Red}   = refl
only-Blue-is-constant {Green} = refl
#+END_SRC

In such cases, we can encode the general design decisions ---/pattern match and yield refl/---
then apply the schema to each use case.

Here's the schema:
#+BEGIN_SRC org-agda
constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []

by-refls : Name → Term → TC ⊤
by-refls nom thm-you-hope-is-provable-by-refls
 = let mk-cls : Name → Clause
       mk-cls qcolour = clause [ 𝒽𝓇𝒶 (con qcolour []) ] (con (quote refl) [])
   in
   do let η = nom
      δ ← getDefinition (quote RGB)
      let clauses = List.map mk-cls (constructors δ)
      declareDef (𝓋𝓇𝒶 η) thm-you-hope-is-provable-by-refls
      defineFun η clauses
#+END_SRC

Here's a use case.
#+BEGIN_SRC org-agda
_ : ∀{c} → just-Red c ≡ Red
_ = nice
  where unquoteDecl nice = by-refls nice (quoteTerm (∀{c} → just-Red c ≡ Red))
#+END_SRC

Note:
0. The first ~nice~ refers to the function
   created by the RHS of the unquote.

1. The RHS ~nice~ refers to the Name value provided
   by the LHS.

2. The LHS ~nice~ is a declaration of a Name value.

This is rather clunky since the theorem to be proven was repeated twice
─repetition is a signal that something's wrong! In the next section we
use macros to avoid such repetiton, as well as the ~quoteTerm~ keyword.

Note that we use a ~where~ clause since unquotation cannot occur in a ~let~,
for some reason.

Here's another use case of the proof pattern (•̀ᴗ•́)و
#+BEGIN_SRC org-agda
_ : ∀{c} → only-Blue c ≡ Blue
_ = nice
  where unquoteDecl nice = by-refls nice (quoteTerm ∀{c} → only-Blue c ≡ Blue)
#+END_SRC

One proof pattern, multiple invocations!
Super neat stuff :grin:

* Macros ─Abstracting Proof Patterns

 Macros are functions of type ~τ₀ → τ₁ → ⋯ → Term → TC ⊤~ that are defined in a
 ~macro~ block. The last argument is supplied by the type checker and denotes
 the “goal” of where the macro is placed: One generally unifies what they have
 with the goal, what is desired in the use site.

 Why the ~macro~ block?
 + Metaprograms can be run in a term position.
 + Without the macro block, we run computations using the ~unquote~ keyword.
 + Quotations are performed automatically; e.g.,
   if ~f : Term → Name → Bool → Term → TC ⊤~
   then an application ~f u v w~ desugars into
   ~unquote (f (quoteTerm u) (quote v) w)~.

   No syntactic overhead: Macros are applied like normal functions.

Macros cannot be recursive; instead one defines a recursive function outside the
macro block then has the macro call the recursive function.

** C-style macros

In the C language one defines a macro, say, by ~#define luckyNum 1972~ then later uses
it simply by the name ~luckyNum~. Without macros, we have syntactic overhead using
the ~unquote~ keyword:
#+BEGIN_SRC org-agda
luckyNum₀ : Term → TC ⊤
luckyNum₀ h = unify h (quoteTerm 55)

num₀ : ℕ
num₀ = unquote luckyNum₀
#+END_SRC
Instead, we can achieve C-style behaviour by placing our metaprogramming code within a ~macro~ block.
#+BEGIN_SRC org-agda
macro
  luckyNum : Term → TC ⊤
  luckyNum h = unify h (quoteTerm 55)

num : ℕ
num = luckyNum
#+END_SRC
Unlike C, all code fragments must be well-defined.

*Exercise:* Write a macro to always yield the first argument in a function.
The second example shows how it can be used to access implicit arguments
without mentioning them :b
#+BEGIN_EXAMPLE org-agda
macro
  first : Term → TC ⊤
  first goal = ⋯

myconst : {A B : Set} → A → B → A
myconst = λ x → λ y → first

mysum : ( {x} y : ℕ) → ℕ
mysum y = y + first
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC org-agda
{- exercise -}
macro
  first : Term → TC ⊤
  first goal = unify goal (var 1 [])

myconst : {A B : Set} → A → B → A
myconst = λ x → λ y → first

mysum : ( {x} y : ℕ) → ℕ
mysum y = y + first
{- end -}
#+END_SRC
:End:

** Tedious Repetitive Proofs No More!
Suppose we wish to prove that addition, multiplication, and exponentiation
have right units 0, 1, and 1 respectively. We obtain the following nearly identical
proofs!

#+BEGIN_SRC org-agda
+-rid : ∀{n} → n + 0 ≡ n
+-rid {zero}  = refl
+-rid {suc n} = cong suc +-rid

*-rid : ∀{n} → n * 1 ≡ n
*-rid {zero}  = refl
*-rid {suc n} = cong suc *-rid

^-rid : ∀{n} → n ^ 1 ≡ n
^-rid {zero}  = refl
^-rid {suc n} = cong suc ^-rid
#+END_SRC

There is clearly a pattern here screaming to be abstracted, let's comply ♥‿♥

The natural course of action in a functional language is to try a higher-order combinator:
#+BEGIN_SRC org-agda
{- “for loops” or “Induction for ℕ” -}
foldn : (P : ℕ → Set) (base : P zero) (ind : ∀ n → P n → P (suc n))
      → ∀(n : ℕ) → P n
foldn P base ind zero    = base
foldn P base ind (suc n) = ind n (foldn P base ind n)
#+END_SRC

Now the proofs are shorter:
#+BEGIN_SRC org-agda
_ : ∀ (x : ℕ) → x + 0 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- This and next two are the same -}

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- Yup, same proof as previous -}

_ : ∀ (x : ℕ) → x ^ 1 ≡ x
_ = foldn _ refl (λ _ → cong suc)    {- No change, same proof as previous -}
#+END_SRC
Unfortunately, we are manually copy-pasting the same proof /pattern/.
#+begin_quote org
When you see repetition, copy-pasting, know that there is room for improvement! (•̀ᴗ•́)و

Don't repeat yourself!
#+end_quote

Repetition can be mitigated a number of ways, including typeclasses or metaprogramming, for example.
The latter requires possibly less thought and it's the topic of this article, so let's do that :smile:

*Exercise*: Following the template of the previous exercises, fill in the missing parts below.
Hint: It's nearly the same level of difficulty as the previous exercises.
#+BEGIN_EXAMPLE org-agda
make-rid : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Name → TC ⊤
make-rid _⊕_ e nom
 = do ⋯

_ : ∀{x : ℕ} → x + 0 ≡ x
_ = nice where unquoteDecl nice = make-rid _+_ 0 nice
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC org-agda
make-rid : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Name → TC ⊤
make-rid _⊕_ e nom
 = do let η = nom
      let clauses =   clause [ 𝒽𝓇𝒶 (con (quote zero) []) ] (con (quote refl) [])
                    ∷ clause [ 𝒽𝓇𝒶 (con (quote suc)  [ 𝓋𝓇𝒶 (var "n") ]) ]
                             (def (quote cong) (𝓋𝓇𝒶 (quoteTerm suc) ∷ 𝓋𝓇𝒶 (def nom []) ∷ [])) ∷ []
      τ ← quoteTC (∀{x : ℕ} → x ⊕ e ≡ x)
      declareDef (𝓋𝓇𝒶 η) τ
      defineFun η clauses

_ : ∀{x : ℕ} → x + 0 ≡ x
_ = nice where unquoteDecl nice = make-rid _+_ 0 nice
#+END_SRC
:End:

There's too much syntactic overhead here, let's use macros instead.
#+BEGIN_SRC org-agda
macro
  _trivially-has-rid_ : (let A = ℕ) (_⊕_ : A → A → A) (e : A) → Term → TC ⊤
  _trivially-has-rid_ _⊕_ e goal
   = do τ ← quoteTC (λ(x : ℕ) → x ⊕ e ≡ x)
        unify goal (def (quote foldn)            {- Using foldn    -}
          ( 𝓋𝓇𝒶 τ                                {- Type P         -}
          ∷ 𝓋𝓇𝒶 (con (quote refl) [])            {- Base case      -}
          ∷ 𝓋𝓇𝒶 (λ𝓋 "_" ↦ quoteTerm (cong suc))  {- Inductive step -}
          ∷ []))
#+END_SRC

Now the proofs have minimal repetition /and/ the proof pattern is written only /once/:
#+BEGIN_SRC org-agda
_ : ∀ (x : ℕ) → x + 0 ≡ x
_ = _+_ trivially-has-rid 0

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = _*_ trivially-has-rid 1

_ : ∀ (x : ℕ) → x * 1 ≡ x
_ = _^_ trivially-has-rid 1
#+END_SRC

Note we could look at the type of the goal, find the operator ~_⊕_~ and the unit;
they need not be passed in. Later we will see how to reach into the goal type
and pull pieces of it out for manipulation (•̀ᴗ•́)و

It would have been ideal if we could have defined our macro without using ~foldn~;
I could not figure out how to do that. 😧

Before one abstracts a pattern into a macro, it's useful to have a few instances
of the pattern beforehand. When abstracting, one may want to compare how we think
versus how Agda's thinking. For example, you may have noticed that in the previous
macro, Agda normalised the expression ~suc n + 0~ into ~suc (n + 0)~ by invoking the definition
of ~_+_~. We may inspect the goal of a function with the ~quoteGoal ⋯ in ⋯~ syntax:

#+BEGIN_SRC org-agda
+-rid′ : ∀{n} → n + 0 ≡ n
+-rid′ {zero}  = refl
+-rid′ {suc n} = quoteGoal e in
  let
    suc-n : Term
    suc-n = con (quote suc) [ 𝓋𝓇𝒶 (var 0 []) ]

    lhs : Term
    lhs = def (quote _+_) (𝓋𝓇𝒶 suc-n ∷ 𝓋𝓇𝒶 (lit (nat 0)) ∷ [])

    {- Check our understanding of what the goal is “e”. -}
    _ : e ≡ def (quote _≡_)
                 (𝒽𝓇𝒶 (quoteTerm Level.zero) ∷ 𝒽𝓇𝒶 (quoteTerm ℕ)
                 ∷ 𝓋𝓇𝒶 lhs ∷ 𝓋𝓇𝒶 suc-n ∷ [])
    _ = refl

    {- What does it look normalised. -}
    _ :   quoteTerm (suc (n + 0) ≡ n)
         ≡ unquote λ goal → (do g ← normalise goal; unify g goal)
    _ = refl
  in
  cong suc +-rid′
#+END_SRC

It would be really nice to simply replace the last line by a macro, say ~induction~.
Unfortunately, for that I would need to obtain the name ~+-rid′~, which as far as I could
tell is not possible with the current reflection mechanism.

* Our First Real Proof Tactic

When we have a proof ~p : x ≡ y~ it is a nuisance to have to write ~sym p~ to prove ~y ≡ x~
─we have to remember which ‘direction’ ~p~. Let's alleviate such a small burden, then use
the tools here to alleviate a larger burden later; namely, rewriting subexpressions.

Given ~p : x ≡ y~, we cannot simply yield ~def (quote sym) [ 𝓋𝓇𝒶 p ]~ since ~sym~ actually
takes four arguments ─compare when we quoted ~_≡_~ earlier. Instead, we infer type of ~p~
to be, say, ~quoteTerm (_≡_ {ℓ} {A} x y)~. Then we can correctly provide all the required arguments.

#+BEGIN_SRC org-agda
≡-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-type-info (def (quote _≡_) (𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ [])) = returnTC (𝓁 , 𝒯 , l , r)
≡-type-info _ = typeError [ strErr "Term is not a ≡-type." ]
#+END_SRC

What if later we decided that we did not want a proof of ~x ≡ y~, but rather of ~x ≡ y~.
In this case, the orginal proof ~p~ suffices. Rather than rewriting our proof term, our
macro could try providing it if the symmetry application fails.

#+BEGIN_SRC org-agda
{- Syntactic sugar for trying a computation, if it fails then try the other one -}
try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f
#+END_SRC

With the setup in hand, we can now form our macro:
#+BEGIN_SRC org-agda
macro
  apply₁ : Term → Term → TC ⊤
  apply₁ p goal = try (do τ ← inferType p
                          𝓁 , 𝒯 , l , r ← ≡-type-info τ
                          unify goal (def (quote sym) (𝓁 ∷ 𝒯 ∷ 𝒽𝓇𝒶 l ∷ 𝒽𝓇𝒶 r ∷ 𝓋𝓇𝒶 p ∷ [])))
                  or-else
                       unify goal p
#+END_SRC

For example,
#+BEGIN_SRC org-agda
postulate x y : ℕ
postulate q : x + 2 ≡ y

{- Same proof yields two theorems! (งಠ_ಠ)ง -}
_ : y ≡ x + 2
_ = apply₁ q

_ : x + 2 ≡ y
_ = apply₁ q
#+END_SRC

Let's furnish ourselves with the ability to inspect the /produced/ proofs.
#+BEGIN_SRC org-agda
{- Type annotation -}
syntax has A a = a ∶ A -- “\:”

has : ∀ (A : Set) (a : A) → A
has A a = a
#+END_SRC

Let's try this on an arbitrary type:
#+BEGIN_SRC org-agda
woah : {A : Set} (x y : A) → x ≡ y → (y ≡ x) × (x ≡ y)
woah x y p = apply₁ p , apply₁ p

  where -- Each invocation generates a different proof, indeed:

  first-pf : (apply₁ p ∶ (y ≡ x)) ≡ sym p
  first-pf = refl

  second-pf : (apply₁ p ∶ (x ≡ y)) ≡ p
  second-pf = refl
#+END_SRC

*Exercise:* When we manually form a proof invoking symmetry we simply write, for example, ~sym p~
and the implict arguments are inferred. We can actually do the same thing here! We were a bit dishonest above. 👂
Rewrite ~apply₁~, call it ~apply₂, so that the ~try~ block is a single, unparenthesised, ~unify~ call.
:Solution:
#+BEGIN_SRC org-agda
macro
  apply₂ : Term → Term → TC ⊤
  apply₂ p goal = try unify goal (def (quote sym)  (𝓋𝓇𝒶 p ∷ []))
                  or-else unify goal p

_ : {A : Set} (x y : A) → x ≡ y → (y ≡ x) × (x ≡ y)
_ = λ x y p → apply₂ p , apply₂ p
#+END_SRC
:End:

*Exercise:* Extend the previous macro so that we can prove statements of the form ~x ≡ x~ regardless of what ~p~
proves. Aesthetics hint: ~try_or-else_~ doesn't need brackets in this case, at all.
#+BEGIN_EXAMPLE org-agda
macro
  apply₃ : Term → Term → TC ⊤
  apply₃ p goal = ⋯

yummah : {A : Set} {x y : A} (p : x ≡ y)  →  x ≡ y  ×  y ≡ x  ×  y ≡ y
yummah p = apply₃ p , apply₃ p , apply₃ p
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC org-agda
macro
  apply₃ : Term → Term → TC ⊤
  apply₃ p goal = try unify goal (def (quote sym) (𝓋𝓇𝒶 p ∷ []))
                  or-else try unify goal p
                          or-else unify goal (con (quote refl) [])

yummah : {A : Set} {x y : A} (p : x ≡ y)  →  x ≡ y  ×  y ≡ x  ×  y ≡ y
yummah p = apply₃ p , apply₃ p , apply₃ p
#+END_SRC
:End:

*Exercise:* Write the following seemingly silly macro.
Hint: You cannot use the ~≡-type-info~ method directly, instead you must invoke ~getType~ beforehand.
#+BEGIN_EXAMPLE org-agda
≡-type-info′ : Name → TC (Arg Term × Arg Term × Term × Term)
≡-type-info′ = ⋯

macro
  sumSides : Name → Term → TC ⊤
  sumSides n goal = ⋯

_ : sumSides q ≡ x + 2 + y
_ = refl
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC org-agda
≡-type-info′ : Name → TC (Arg Term × Arg Term × Term × Term)
≡-type-info′ n = do τ ← getType n; ≡-type-info τ

macro
  sumSides : Name → Term → TC ⊤
  sumSides n goal = do _ , _ , l , r ← ≡-type-info′ n; unify goal (def (quote _+_) (𝓋𝓇𝒶 l ∷ 𝓋𝓇𝒶 r ∷ []))

_ : sumSides q ≡ x + 2 + y
_ = refl
#+END_SRC
:End:

* TODO COMMENT ideas

+ macros left and right for ≡-type.

+ flatten: Take a nested record hierarchy and produce a flattened telescope, since
  records cannot be unquotes.

+ 2^50 * 3^313 ≡  3^313 * 2^50 is true by symmetry of *,
  but may timeout if we try to prove things by refl.

* COMMENT README

C-c C-c: evalute src block

#+NAME: make-readme
#+BEGIN_SRC emacs-lisp :results none
(with-temp-buffer
    (insert
    "#+EXPORT_FILE_NAME: README.md
     # HTML: <h1> gentle-intro-to-reflection </h1>

     A slow-paced introduction to reflection in Agda. ---Tactics!

     # The following can also be read as a [[https://alhassy.github.io/literate/][blog post]].

     # TOC: headlines 2
     #+INCLUDE: gentle-intro-to-reflection.lagda
    ")
    (org-mode)
    (org-md-export-to-markdown)
)
#+END_SRC

* COMMENT footer

The org-agda-mode and literate.el come from:
https://github.com/alhassy/org-agda-mode

# Having this with the local variables causes trees
# to remain folded when moving to agda2-mode.
#
(progn (org-babel-goto-named-src-block "make-readme") (org-babel-execute-src-block) (outline-hide-sublevels 1))

# Local Variables:
# eval: (visual-line-mode t)
# eval: (load-file "~/org-agda-mode/org-agda-mode.el")
# eval: (load-file "~/org-agda-mode/literate.el")
# End:
