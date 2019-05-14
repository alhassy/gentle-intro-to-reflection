# | ~C-x C-a~ | transform org ~org-agda~ blocks to literate Agda blocs        |
# | ~C-x C-o~ | transform literate Agda code delimiters to org ~org-agda~ src |
#
#+TITLE: A Gentle Introduction to Reflection in Agda
#+DESCRIPTION: How can we use a single proof to prove two different theorems?
#+AUTHOR: Musa Al-hassy
#+EMAIL: alhassy@gmail.com
#+STARTUP: indent

#+CATEGORIES: Agda Org Emacs
#+OPTIONS: html-postamble:nil toc:nil
#+IMAGE: ../assets/img/org_logo.png
#+SOURCE: https://raw.githubusercontent.com/alhassy/org-agda-mode/master/literate.lagda

# INCLUDE: ~/Dropbox/MyUnicodeSymbols.org

* Abstract       :ignore:
#+BEGIN_CENTER
*Abstract*
#+END_CENTER

/One proof for two different theorems!/

Let's learn how we can do that in Agda.

This tutorial is the result of mostly experimenting with the
[[https://agda.readthedocs.io/en/v2.5.2/language/reflection.html][documentation]] on Agda's reflection mechanism, which essentially
only exposes the reflection interface and provides a few tiny examples.

Everything here works with Agda version 2.6.0.

* Imports

#+BEGIN_SRC org-agda
module gentle-intro-to-reflection where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Reflection hiding (_≟_ ; name)
open import Data.List
open import Relation.Nullary

open import Data.Nat
open import Data.Bool
open import Data.String

open import Data.Unit

import Level as Level

open import Data.Product
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



** Example: Simple Terms

The first example below demonstrates that ~true~ is a type “con”structor
that takes no arguments, whence the ~[]~.
#+BEGIN_SRC org-agda
_ : quoteTerm true ≡ con (quote true) []
_ = refl

_ : quoteTerm 1 ≡ lit (nat 1)
_ = refl

_ :    quoteTerm (suc zero)
     ≡ con (quote suc) (arg (arg-info visible relevant) (quoteTerm zero) ∷ [])
_ = refl

{- Using our helper 𝓋𝓇𝒶 -}
_ : quoteTerm (suc zero) ≡ con (quote suc) (𝓋𝓇𝒶 (quoteTerm zero) ∷ [])
_ = refl
#+END_SRC

** Example: Simple Types
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

* COMMENT Monad Setup

#+BEGIN_SRC org-agda
_>>=_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_        : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
_>>_  = λ p q → p >>= (λ _ → q)
#+END_SRC
* COMMENT Two theorems from a proof of ~x + 2 ≡ y~

Suppose we have the following theorem ~p~.
#+BEGIN_SRC org-agda
postulate
  x y : ℕ
  p   : x + 2 ≡ y
#+END_SRC

Let's make some helpful abbreviations.
#+BEGIN_SRC org-agda
𝓁₀ = arg (arg-info hidden relevant) (def (quote Level.zero) [])
𝒩 = arg (arg-info hidden relevant) (def (quote ℕ) [])
#+END_SRC

* COMMENT A Spec environment
Here's a literate Agda ~spec~-ification environment, which corresponds to an Org-mode ~EXAMPLE~ block.
#+BEGIN_EXAMPLE org-agda
module this-is-a-spec {A : Set} (_≤_ : A → A → Set) where

  maximum-specfication : (candidate : A) → Set
  maximum-specfication c = ?
#+END_EXAMPLE

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

     #+TOC: headlines 2
     #+INCLUDE: gentle-intro-to-reflection.lagda
    ")
    (org-mode)
    (org-md-export-to-markdown)
)
#+END_SRC

* COMMENT footer

(progn (org-babel-goto-named-src-block "make-readme") (org-babel-execute-src-block) (outline-hide-sublevels 1))

Repo: https://github.com/alhassy/org-agda-mode

# Local Variables:
# eval: (visual-line-mode t)
# eval: (load-file "~/org-agda-mode/org-agda-mode.el")
# eval: (load-file "~/org-agda-mode/literate.el")
# End:
