structure KernelTypes =
struct

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness (an interactive session may
    create more than one such pair, and they need to be distinguished).
 ---------------------------------------------------------------------------*)

type id = KernelSig.kernelid;

(*---------------------------------------------------------------------------*
 * HOL types are somewhat akin to terms in first order logic.                *
 *---------------------------------------------------------------------------*)

datatype hol_type = Tyv of string
                  | Tyapp of id * hol_type list;

(*---------------------------------------------------------------------------*
 * HOL terms                                                                 *
 *---------------------------------------------------------------------------*)

type const_info = (id * hol_type);

datatype term = Var of string * hol_type
              | App of term * term
              | Const of const_info
              | Abs of term * term;

end
