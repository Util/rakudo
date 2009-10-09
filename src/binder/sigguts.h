/* Flags that can be set on a signature element. */
#define SIG_ELEM_BIND_CAPTURE      1
#define SIG_ELEM_BIND_PRIVATE_ATTR 2
#define SIG_ELEM_BIND_PUBLIC_ATTR  4
#define SIG_ELEM_SLURPY_POS        8
#define SIG_ELEM_SLURPY_NAMED      16
#define SIG_ELEM_SLURPY_BLOCK      32
#define SIG_ELEM_INVOCANT          64
#define SIG_ELEM_MULTI_INVOCANT    128
#define SIG_ELEM_IS_RW             256
#define SIG_ELEM_IS_COPY           512
#define SIG_ELEM_IS_REF            1024
#define SIG_ELEM_IS_OPTIONAL       2048


/* Data structure to describe a single element in the signature. */
typedef struct llsig_element {
    STRING *variable_name;    /* The name in the lexpad to bind to, if any. */
    PMC    *named_names;      /* List of the name(s) that a named parameter has. */
    PMC    *type_captures;    /* Name(s) that we bind the type of a parameter to. */
    INTVAL flags;             /* Various flags about the parameter. */
    PMC    *nominal_type;     /* The nominal type of the parameter. */
    PMC    *post_constraints; /* Junction of any extra constraints. */
    PMC    *sub_signature;    /* Any nested signature. */
} llsig_element;


/* Flags we can set on the Context PMC.
 *
 * ALREADY_CHECKED indicates that we have determined that all of the arguments
 * can be bound to positional parameters without any further type checking
 * (because the multi-dispatch cache told us so) and any named parameters are
 * automatically going into the named slurpy variable.
 *
 * ALREADY_BOUND indicates that the variables have already been bound into the
 * lexpad and means the bind_signature op is thus a no-op. This happens if we
 * had to do a bindability check in the multi-dispatch anyway.
 */
#define PObj_P6S_ALREADY_CHECKED_FLAG   PObj_private0_FLAG
#define PObj_P6S_ALREADY_BOUND_FLAG     PObj_private1_FLAG


/* A function we want to share to provide the interface to the binder. */
INTVAL
Rakudo_binding_bind_signature(PARROT_INTERP, PMC *lexpad, PMC *signature,
                              PMC *pos_args, PMC *named_args,
                              INTVAL no_nom_type_check, STRING **error);