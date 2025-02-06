# Multivariate Recursive Domain Equations in Coq
_Accompanying Coq sources for the paper: Solving Multivariate Recursive Domain Equations in Coq_

A Coq formalization and solver for general multivariate recursive domain
equations, enabling the construction and verification of solutions for
recursive structures in programming language semantics and formal methods.

## Requirements and compilation instructions
The Coq formalization does not have any dependencies beyond Coq itself. The
formalization has been tested with Coq version 8.20.0 compiled with OCaml
version 5.2.1.

To compile the formalization, run the following command in the root directory of
the repository:

```bash
make -j[n]
```
where `[n]` is the number of CPU cores to use for compilation.

## Structure
The source code for the paper is located in the [**theories**](theories) folder and is structured as follows:
- [**prelude**](theories/prelude)
    - `axioms.v` -- Axioms used in the formalization.
- [**category-theory**](theories/category-theory)
    - `category.v` -- Definition of a category and common instances and properties.
    - `functor.v` -- Definition of a functor and common instances and properties.
    - `isomorphism.v` -- Definition of an isomorphism and properties.
    - `natural_transformation.v` -- Definition of a natural transformation and properties.
    - `category_theory.v` -- Wrapper that exports all the contents of the `category-theory` folder.
    - [**instances**](theories/category-theory/instances)
        - [**categories**](theories/category-theory/instances/categories)
            - `type.v` -- Definition of the category of types.
        - [**functors**](theories/category-theory/instances/functors)
            - `const.v` -- Definition of the constant functor.
            - `hom.v` -- Definition of the hom-functor.
            - `product.v` -- Definition of the product functor.
        - [**structure**](theories/category-theory/instances/structure)
            - `type_ccc.v` -- Proof that the category of types is a cartesian closed category.
    - [**structure**](theories/category-theory/structure)
        - `initial.v` -- Definition of a category with an initial object.
        - `terminal.v` -- Definition of a category with a terminal object.
        - `finite_products.v` -- Definition of a category with finite products.
        - `closed.v` -- Definition of a cartesian closed category.
        - `structure.v` -- Wrapper that exports all the contents of the `structure` folder.
- [**ofe**](theories/ofe)
    - `ofe.v` -- Definition of ordered families of equivalences, non-expansive functions, and contractive functions.
    - `banach.v` -- Proof that the Banach fixed-point theorem holds for contractive functions.
    - [**ofe-cat**](theories/ofe/ofe-cat)
        - `ofe_cat.v` -- Wrapper that exports all the contents of the `ofe-cat` folder.
        - [**categories**](theories/ofe/ofe-cat/categories)
            - `OFE.v` -- Definition of the category of ordered families of equivalences.
            - `COFE.v` -- Definition of the category of complete ordered families of equivalences.
            - `iCOFE.v` -- Definition of the category of inhabited complete ordered families of equivalences.
        - [**functors**](theories/ofe/ofe-cat/functors)
            - `later.v` -- Definition of the later functor and its properties.
        - [**structure**](theories/ofe/ofe-cat/structure)
            - `ofe_ccc.v` -- Proof that the category of ordered families of equivalences is a cartesian closed category.
            - `cofe_ccc.v` -- Proof that the category of complete ordered families of equivalences is a cartesian closed category.
            - `icofe_ccc.v` -- Proof that the category of inhabited complete ordered families of equivalences is a cartesian closed category.
            - `icofe_monoidal.v` -- Proof that the category of inhabited complete ordered families of equivalences is a monoidal category.
- [**ecategory-theory**](theories/ecategory-theory)
    - `ecategory.v` -- Definition of a category enriched over the category of iCOFEs and common instances and properties.
    - `efunctor.v` -- Definition of an enriched functor over the category of iCOFEs and common instances and properties.
    - `ealgebra.v` -- Definition of an enriched algebra over the category of iCOFEs and common instances and properties.
    - `eisomorphism.v` -- Definition of an enriched isomorphism over the category of iCOFEs and common instances and properties.
- [**solver**](theories/solver)
    - `econtractive.v` -- Definition of locally contractive functors.
    - `elater.v` -- Definition of the later functor in the enriched setting.
    - `partial_econtractive.v` -- Definition of partially locally contractive functors.
    - `ectr_compl.v` -- Definition of a contractively complete iCOFE-enriched category.
    - `join_split.v` -- Definition of the auxiliary join and split iCOFE-enriched functors.
    - `esym.v` -- Definition of the symmetrization of a iCOFE-enriched functor.
    - `muF.v` -- Definition of the muF functor and its properties.
    - `general_america_rutten.v` -- Proof of the general America-Rutten theorem for any contractively complete iCOFE-enriched category.
    - `general_existence.v` -- Proof of the general existence theorem for multivariate recursive domain equations.
    - [**instances**](theories/solver/instances)
        - `einstances.v` -- Definition of the self-enriched category of iCOFEs and the later category of an iCOFE-enriched category.
        - `eicofe_ctr_compl.v` -- Proof that the category of inhabited complete ordered families of equivalences is contractively complete.
- [**examples**](theories/ofe/examples)
    - `cons.v` -- Definition of the ofe of infinite sequences and the proof that it is not globally contractive but it is contractively in the second argument.


## Differences between the formalization and the paper
There are a number of small differences between the paper presentation and the
formalization in Coq, that are briefly discussed here.

### Pullbacks vs. Products
In the paper we present the product of two objects in the category of OFEs as
the pullback of the two unique morphisms to the terminal object. This is an easy
way to see that the category of OFEs has all finite limits. However, in the
formalization we do not make use of this property and therefore we define
directly the product of two objects without mentioning pullbacks.

### Results in the Enriched Setting
Although every result in Section 3 is presented in a classical category theory
setting, the formalization is done in the enriched setting. This is because the
results in the enriched setting are more general and can be applied to a wider
range of problems. Moreover, it heavily simplifies the formalization as we can
work with just one definition of locally contractive functors instead of many
of them adapted to different categories.  The following results are presented
in the enriched setting in the formalization:

- **eiCOFE vs. iCOFE**: In the paper we used the term the category of inhabited
complete OFEs (iCOFEs) to refer to the category of iCOFEs and the self-enriched
category of iCOFEs. Although, they are conceptually the same, in the formalization
they are represented by two different structures. The first one is presented in
the [`iCOFE.v`](ofe/ofe-cat/categories/iCOFE.v) file and the second one in the
[`einstances.v`](solver/instances/einstances.v) file.


- **eiCOFE is contractively complete**: This is the content of the [`eicofe_ctr_compl.v`](solver/instances/eicofe_ctr_compl.v)
file. The proof is conceptually the same as the one presented in the paper for the
category of iCOFEs, but adapted to the enriched setting.

- **America-Rutten Theorem vs. General America-Rutten Theorem**:
In the paper we present the America-Rutten theorem for the category of inhabited
complete OFEs (Theorem 3.7). However, in the formalization we present a more
general version of the theorem that holds for any contractively complete
iCOFE-enriched category. This is the content of the [`general_america_rutten.v`](solver/general_america_rutten.v) file.
The proof is conceptually the same as the one presented in the paper, but it
covers a more general setting.

## Paper-to-Coq Correspondence Guide
| **Definition / Theorem**   |      **Paper**      | **File** | **Name of formalization** | **Notation** |
|:--------------------------:|:-------------------:|:--------:|:-------------------------:|:------------:|
| Ordered Families of Equivalences |  Page 2, Definition 2.1 | [`ofe.v`](theories/ofe/ofe.v) | `Record ofe` |  |
| Non-expansive functions |  Page 2, Definition 2.3 | [`ofe.v`](theories/ofe/ofe.v) | `Record NonExpansiveMaps` | `A -n> B`  |
| Category of OFEs | Mentioned in page 3 | [`OFE.v`](theories/ofe/ofe-cat/categories/OFE.v) | `Definition OFE` |  |
| Terminal object in OFE[^1] | Page 3, Lemma 2.5 | [`ofe_ccc.v`](theories/ofe/ofe-cat/structure/ofe_ccc.v) | `Instance  OFE_Terminal` |  |
| Product object in OFE[^1] | Page 3, Lemma 2.6 | [`ofe_ccc.v`](theories/ofe/ofe-cat/structure/ofe_ccc.v)| `Instance OFE_Product` |  |
| Exponential object in OFE[^1] | Page 3, Lemma 2.7 | [`ofe_ccc.v`](theories/ofe/ofe-cat/structure/ofe_ccc.v) | `Instance OFE_CCC` |  |
| Later EndoFunctor[^2] |  Page 6, Definition 3.8 | [`later.v`](theories/ofe/ofe-cat/functors/later.v) | `Instance OFE_Later` |  |
| Cauchy Chain | Page 4, Definition 2.11 | [`ofe.v`](theories/ofe/ofe.v) | `Record cchain` |  |
| Category of COFEs | Mentioned in page 4 | [`COFE.v`](theories/ofe/ofe-cat/categories/COFE.v) | `Definition COFE` |  |
| Contractive functions |  Page 2, Definition 2.12 | [`ofe.v`](theories/ofe/ofe.v) | `Record ContractiveMaps` | `A -c> B`  |
| Partially Contractive functions[^3] |  Page 4, Definition 2.17 | [`ofe.v`](theories/ofe/ofe.v) | `Definition ContractiveFst` | `A -c> B`  |
| Banach Fixed-Point Theorem |  Page 5, Theorem 2.21 | [`banach.v`](theories/ofe/banach.v) | `Theorem ibanach_fixed_point` |  |

[^1]: The terminal object, product object and exponential object are in the category of OFEs are the same as the ones for COFEs and iCOFEs, but they need to be defined separately because of the different definitions of the categories, see [`cofe_ccc.v`](theories/ofe/ofe-cat/structure/cofe_ccc.v) and [`icofe_ccc.v`](theories/ofe/ofe-cat/structure/icofe_ccc.v) for the definitions

[^2]: The later endofunctor is defined in the classical category theory setting
    for the category of OFEs, COFEs and iCOFEs, but it is also defined in the
    enriched setting for the category of eiCOFEs in the
    [`elater.v`](theories/solver/elater.v) file.

[^3]: The definition of partially contractive in the second argument not mentioned explicitly in the paper, but it is also defined in the formalization, see [`ofe.v`](theories/ofe/ofe.v) `Definition ContractiveSnd`.