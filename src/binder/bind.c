/*
$Id$
Copyright (C) 2009, The Perl Foundation.
*/

#define PARROT_IN_EXTENSION
#include "parrot/parrot.h"
#include "parrot/extend.h"
#include "bind.h"

/* Binds a single argument into the lexpad, after doing any checks that are
 * needed. Also handles any type captures. If there is a sub signature, then
 * re-enters the binder. Returns 0 if binding fails, and non-zero otherwise. */
INTVAL
Rakudo_binding_bind_one_param(PARROT_INTERP, PMC *lexpad, llsig_element *sig_info,
                              PMC *value, INTVAL no_nom_type_check, STRING **error) {
    /* If we need to do a type check, do one. */
    if (!no_nom_type_check) {
        STRING * const ACCEPTS = string_from_literal(interp, "ACCEPTS");
        PMC * const type_obj   = sig_info->nominal_type;
        PMC * accepts_meth     = VTABLE_find_method(interp, type_obj, ACCEPTS);
        PMC * result           = (PMC *)Parrot_run_meth_fromc_args(interp,
                accepts_meth, type_obj, ACCEPTS, "PP", value);
        if (!VTABLE_get_integer(interp, result)) {
            /* Type check failed. However, for language inter-op, we do some
             * extra checks if the type is just Positional, Associative, or
             * Callable and the thingy we have matches those enough. */
            /* XXX TODO: Implement language interop checks. */
            /* XXX TODO: Good type check error message. */
            /* XXX TODO: Junction auto-threading failover here??? */
            if (error)
                *error = string_from_literal(interp, "Nominal type check failed");
            return 0;
        }

        /* Handle any constraint types too. */
        if (!PMC_IS_NULL(sig_info->post_constraints)) {
            PMC * const cons_type = sig_info->post_constraints;
            accepts_meth          = VTABLE_find_method(interp, cons_type, ACCEPTS);
            result                = (PMC *)Parrot_run_meth_fromc_args(interp,
                accepts_meth, cons_type, ACCEPTS, "PP", value);
            if (!VTABLE_get_integer(interp, result)) {
                /* XXX TODO: Good type check error message. */
                if (error)
                    *error = string_from_literal(interp, "Constraint type check failed");
                return 0;
            }
        }
    }
    
    /* Do we have any type captures to bind? */
    if (!PMC_IS_NULL(sig_info->type_captures)) {
        /* Obtain type object. */
        STRING * const WHAT   = string_from_literal(interp, "ACCEPTS");
        PMC * const what_meth = VTABLE_find_method(interp, value, WHAT);
        PMC * const type_obj  = (PMC *)Parrot_run_meth_fromc_args(interp,
                what_meth, value, WHAT, "P");

        /* Iterate over symbols we need to bind this to, and bind 'em. */
        PMC * const iter = VTABLE_get_iter(interp, sig_info->type_captures);
        while (VTABLE_get_bool(interp, iter)) {
            STRING *name = VTABLE_shift_string(interp, iter);
            VTABLE_set_pmc_keyed_str(interp, lexpad, name, type_obj);
        }
    }

    /* Is it "is rw"? */
    if (sig_info->flags & SIG_ELEM_IS_RW) {
        /* XXX TODO Check if rw flag is set, after rw refactor is done. */
        /* If it has a name, bind it into the lexpad. */
        if (sig_info->variable_name)
            VTABLE_set_pmc_keyed_str(interp, lexpad, sig_info->variable_name, value);
    }
    else if (sig_info->flags & SIG_ELEM_IS_REF) {
        /* XXX TODO Implement is ref. */
        if (error)
            *error = string_from_literal(interp, "is ref not yet implemented");
        return 0;
    }
    else if (sig_info->flags & SIG_ELEM_IS_COPY) {
        /* Clone the value, wrap it into an ObjectRef, and bind it. */
        if (sig_info->variable_name) {
            PMC *copy = VTABLE_clone(interp, value);
            PMC *ref  = pmc_new_init(interp, pmc_type(interp,
                    string_from_literal(interp, "ObjectRef")), copy);
            VTABLE_set_pmc_keyed_str(interp, lexpad, sig_info->variable_name, ref);
        }
    }
    else {
        /* Read only. Wrap it into a ObjectRef, mark readonly and bind it. */
        if (sig_info->variable_name) {
            PMC *ref  = pmc_new_init(interp, pmc_type(interp,
                    string_from_literal(interp, "ObjectRef")), value);
            VTABLE_setprop(interp, ref, string_from_literal(interp, "readonly"), ref);
            VTABLE_set_pmc_keyed_str(interp, lexpad, sig_info->variable_name, ref);
        }
    }

    /* If it has a sub-signature, bind that. */
    if (sig_info->sub_signature) {
        /* XXX TODO: Fill out how we obtain pos_args and named_args, or I
         * guess probably just a capture. But otherwise, it's just a case
         * of recursing. */
        if (error)
            *error = string_from_literal(interp, "Sub-signatures not yet implemented");
        return 0;
    }

    /* Binding of this parameter was thus successful - we're done. */
    return 42;
}


/* Takes a signature along with positional and named arguments and binds them
 * into the provided lexpad (actually, anything that has a Hash interface will
 * do). Returns 0 if binding fails, and non-zero otherwise. */
INTVAL
PARROT_DYNEXT_EXPORT
Rakudo_binding_bind_signature(PARROT_INTERP, PMC *lexpad,
                              llsig_element **elements, INTVAL num_elements,
                              PMC *pos_args, PMC *named_args,
                              INTVAL no_nom_type_check, STRING **error) {
    INTVAL i;
    INTVAL cur_pos_arg = 0;
    INTVAL num_pos_args = VTABLE_elements(interp, pos_args);

    /* Lazily allocated array of bindings to positionals of nameds. */
    PMC **pos_from_named = NULL;

    /* Build nameds -> position hash for named positional arguments. */
    /* XXX We only need do this on the first binding, not every one - add
     * logic to cache this instead. For extra minor speed win, use Hash
     * directly perhaps, to avoid a level of indirection through the PMC
     * interface. */
    PMC *named_to_pos_cache = pmc_new(interp, enum_class_Hash);
    for (i = 0; i < num_elements; i++) {
        /* If we find a named argument, we're done with the positionals. */
        if (!PMC_IS_NULL(elements[i]->named_names))
            break;

        /* Skip slurpies (may be a slurpy block, so can't just break). */
        if (elements[i]->flags & SIG_ELEM_SLURPY)
            continue;

        /* Provided it has a name... */
        if (elements[i]->variable_name) {
            /* Strip any sigil, then stick in named to positional array. */
            STRING *store = elements[i]->variable_name;
            STRING *sigil = Parrot_str_substr(interp, store, 0, 1, NULL, 0);
            if (Parrot_str_equal(interp, sigil, string_from_literal(interp, "$")) ||
                    Parrot_str_equal(interp, sigil, string_from_literal(interp, "@")) ||
                    Parrot_str_equal(interp, sigil, string_from_literal(interp, "%")))
                store = Parrot_str_substr(interp, store, 1, 0, NULL, 0);
            VTABLE_set_integer_keyed_str(interp, named_to_pos_cache, store, i);
        }
    }

    /* First, consider named arguments, to see if there are any that we will
     * be wanting to bind positionally. */
    if (VTABLE_elements(interp, named_args)) {
        PMC *iter = VTABLE_get_iter(interp, named_args);
        while (VTABLE_get_bool(interp, iter)) {
            STRING *name = VTABLE_shift_string(interp, iter);
            if (VTABLE_exists_keyed_str(interp, named_to_pos_cache, name)) {
                /* Found one. We'll stash it away for quick access to bind it
                 * later. */
                INTVAL pos = VTABLE_get_integer_keyed_str(interp, named_to_pos_cache, name);
                if (!pos_from_named)
                    pos_from_named = mem_sys_allocate_zeroed(sizeof(PMC *) * num_elements);
                pos_from_named[pos] = VTABLE_get_pmc_keyed_str(interp, named_args, name);
            }
        }
    }

    /* Now we'll walk through the signature and go about binding things. */
    for (i = 0; i < num_elements; i++) {
        /* Is it a positional sourced from a named? */
        if (pos_from_named && pos_from_named[i]) {
            /* We have the value - try bind this parameter. */
            if (!Rakudo_binding_bind_one_param(interp, lexpad, elements[i],
                    pos_from_named[i], no_nom_type_check, error))
                return 0;
        }

        /* Otherwise, maybe it's a positional. */
        else if (PMC_IS_NULL(elements[i]->named_names)) {
            /* XXX TODO: Positional binding logic. */
        }

        /* Else, we're into the nameds. */
        else {
            /* XXX TODO: Nameds binding logic. */
        }
    }

    /* If we get here, we're done. */
    return 1;
}

/*
 * Local variables:
 *   c-file-style: "parrot"
 * End:
 * vim: expandtab shiftwidth=4:
 */
