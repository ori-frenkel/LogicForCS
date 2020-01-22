# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

ANTI_QUANTIFIER = {'A': 'E', 'E': 'A'}
QUANTIFIER_AXIOM = {'A': 0, 'E': 1}

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    if is_relation(formula.root):
        return True
    elif is_unary(formula.root):
        return is_quantifier_free(formula.first)

    elif is_binary(formula.root):
        if is_quantifier_free(formula.first) and\
            is_quantifier_free(formula.second):
            return True
        return False

    elif is_quantifier(formula.root):
        return False

    return True


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)

    return is_quantifier_free(formula)




def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    # if the formula is quantifier free, all the variable already unique
    if is_quantifier_free(formula):
        f_f = Formula('->', formula, formula)
        prover.add_tautology(Formula('&', f_f, f_f))
        return formula, prover.qed()

    elif is_unary(formula.root):
        # in the comments here I am will address _formula as formula without the '~'
        # getting the renamed formula and proof without the '~'
        formula_without_not_uniquely_renamed_var, prover2 = uniquely_rename_quantified_variables(
            formula.first)
        # adding the proof of the equivalence of
        # formula_without_not_uniquely_renamed_var to formula without the '~'
        line = prover.add_proof(prover2.conclusion, prover2)

        # wanting to add to the prover that ~formula_without_not_uniquely_renamed_var <-> formula
        # I will mark the above formula as 'formula_wanting_to_add'
        not_formula_unique_var = Formula('~',
                                         formula_without_not_uniquely_renamed_var)

        formula_wanting_to_add = Formula('&',
                                         Formula('->', formula,
                                                 not_formula_unique_var),
                                         Formula('->', not_formula_unique_var,
                                                 formula))

        prover.add_tautological_implication(formula_wanting_to_add, {line})
        return not_formula_unique_var, prover.qed()

    elif is_binary(formula.root):
        formula_first, proof_first = uniquely_rename_quantified_variables(
                                     formula.first)
        formula_second, proof_second = uniquely_rename_quantified_variables(
                                     formula.second)

        line1 = prover.add_proof(proof_first.conclusion, proof_first)
        line2 = prover.add_proof(proof_second.conclusion, proof_second)
        # using tautology implication on
        # formula iff Formula(formula.root, formula_first, formula_second)
        form = Formula(formula.root, formula_first, formula_second)
        formula_wanting_to_add = Formula('&', Formula('->', formula, form),
                                              Formula('->', form, formula))
        prover.add_tautological_implication(formula_wanting_to_add, {line1, line2})
        return form, prover.qed()

    else:
        # quantifier case
        # assert is_quantifier(formula.root)
        i = 14 # i is the axiom we using, for E we using the 16 th axiom and
               #  for A the 15 th axiom
        if formula.root == 'E':
            i = 15
        f_predicate_unique_var, p_predicate_unique_var = \
            uniquely_rename_quantified_variables(formula.predicate)

        line1 = prover.add_proof(p_predicate_unique_var.conclusion,
                                 p_predicate_unique_var)
        # now using Axiom number 16 with the following map.
        new_unique_var = next(fresh_variable_name_generator)
        _map = {'R' : formula.predicate.substitute({
                                        formula.variable : Term.parse('_')}),
                'x': formula.variable,
                'y' : new_unique_var,
                'Q' : f_predicate_unique_var.substitute({
                                        formula.variable : Term.parse('_')})}
        form = ADDITIONAL_QUANTIFICATION_AXIOMS[i].instantiate(_map)
        line2 = prover.add_instantiated_assumption(
            form, ADDITIONAL_QUANTIFICATION_AXIOMS[i], _map)
        prover.add_mp(form.second, line1, line2)
        unique_var_formula = Formula(formula.root, new_unique_var,
                                     f_predicate_unique_var.substitute({
                                        formula.variable : Term.parse(new_unique_var)}))
        return unique_var_formula, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    if is_quantifier(formula.first.root):
        quantified_formula = formula.first
        sub_f = Formula('~', quantified_formula.predicate)
        conclusion, proof = pull_out_quantifications_across_negation(sub_f)
        last_formula = proof.lines[-1].formula
        line1 = prover.add_proof(last_formula, proof)
        anti_quantifier = ANTI_QUANTIFIER[quantified_formula.root]
        axiom = QUANTIFIER_AXIOM[quantified_formula.root]
        _map1 = {'R': quantified_formula.predicate.substitute({
            quantified_formula.variable: Term.parse('_')}),
                'x': quantified_formula.variable}
        f_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom].instantiate(_map1)
        line2 = prover.add_instantiated_assumption(f_axiom,
                        ADDITIONAL_QUANTIFICATION_AXIOMS[axiom], _map1)
        equivalent = Formula(anti_quantifier, quantified_formula.variable,
                             conclusion)
        f1 = Formula('->', formula, equivalent)
        f2 = Formula('->', equivalent, formula)
        conclusion = Formula('&', f1, f2)
        _map2 = {'R': last_formula.first.first.substitute({
            quantified_formula.variable: Term.parse('_')}),
            'Q': last_formula.first.second.substitute({
            quantified_formula.variable: Term.parse('_')}),
            'x': quantified_formula.variable,
            'y': quantified_formula.variable}
        new_conclusion = ADDITIONAL_QUANTIFICATION_AXIOMS[
            -axiom+15].instantiate(_map2)
        line3 = prover.add_instantiated_assumption(new_conclusion,
                        ADDITIONAL_QUANTIFICATION_AXIOMS[-axiom+15], _map2)
        line4 = prover.add_mp(new_conclusion.second, line1, line3)
        line5 = prover.add_tautological_implication(conclusion, {line2,
                                                                  line4})

        return equivalent, prover.qed()

    else:
        f = Formula('->', formula, formula)
        conclusion = Formula('&', f, f)
        prover.add_tautology(conclusion)
        return formula, prover.qed()


def pull_out_quantifications_from_left_across_binary_operator(formula:
                                                              Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    if is_quantifier(formula.first.root):
        quantified_formula = formula.first
        sub_f = Formula(formula.root, quantified_formula.predicate,
                        formula.second)
        conclusion, proof = pull_out_quantifications_from_left_across_binary_operator(sub_f)
        last_formula = proof.lines[-1].formula
        line1 = prover.add_proof(last_formula, proof)
        if formula.root == '&' and quantified_formula.root == 'A':
            axiom = 2
        elif formula.root == '&' and quantified_formula.root == 'E':
            axiom = 3
        elif formula.root == '|' and quantified_formula.root == 'A':
            axiom = 6
        elif formula.root == '|' and quantified_formula.root == 'E':
            axiom = 7
        elif formula.root == '->' and quantified_formula.root == 'A':
            axiom = 10
        else:  # formula.root == '->' and quantified_formula.root == 'E'
            axiom = 11
        _map1 = {'R': quantified_formula.predicate.substitute({
            quantified_formula.variable: Term.parse('_')}),
            'x': quantified_formula.variable, 'Q': formula.second}
        f_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom].instantiate(_map1)
        line2 = prover.add_instantiated_assumption(f_axiom,
                                                   ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                       axiom], _map1)

        if formula.root != '->':
            quantifier = quantified_formula.root
        else:
            quantifier = ANTI_QUANTIFIER[quantified_formula.root]
        equivalent = Formula(quantifier, quantified_formula.variable,
                             conclusion)

        f1 = Formula('->', formula, equivalent)
        f2 = Formula('->', equivalent, formula)
        conclusion = Formula('&', f1, f2)
        _map2 = {'R': last_formula.first.first.substitute({
            quantified_formula.variable: Term.parse('_')}),
            'Q': last_formula.first.second.substitute({
                quantified_formula.variable: Term.parse('_')}),
            'x': quantified_formula.variable,
            'y': quantified_formula.variable}
        index = QUANTIFIER_AXIOM[quantified_formula.root]
        if formula.root == '->':
            index = -index + 1

        new_conclusion = ADDITIONAL_QUANTIFICATION_AXIOMS[
            index + 14].instantiate(_map2)
        line3 = prover.add_instantiated_assumption(new_conclusion,
                                                   ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                       index + 14], _map2)
        line4 = prover.add_mp(new_conclusion.second, line1, line3)
        line5 = prover.add_tautological_implication(conclusion, {line2,
                                                                 line4})

        return equivalent, prover.qed()

    else:
        f = Formula('->', formula, formula)
        conclusion = Formula('&', f, f)
        prover.add_tautology(conclusion)
        return formula, prover.qed()


def pull_out_quantifications_from_right_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    if is_quantifier(formula.second.root):
        quantified_formula = formula.second
        sub_f = Formula(formula.root, formula.first, quantified_formula.predicate)
        conclusion, proof = pull_out_quantifications_from_right_across_binary_operator(sub_f)
        last_formula = proof.lines[-1].formula
        line1 = prover.add_proof(last_formula, proof)
        if formula.root == '&' and quantified_formula.root == 'A':
            axiom = 4
        elif formula.root == '&' and quantified_formula.root == 'E':
            axiom = 5
        elif formula.root == '|' and quantified_formula.root == 'A':
            axiom = 8
        elif formula.root == '|' and quantified_formula.root == 'E':
            axiom = 9
        elif formula.root == '->' and quantified_formula.root == 'A':
            axiom = 12
        else:  # formula.root == '->' and quantified_formula.root == 'E'
            axiom = 13
        _map1 = {'R': quantified_formula.predicate.substitute({
            quantified_formula.variable: Term.parse('_')}),
            'x': quantified_formula.variable, 'Q': formula.first}
        f_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[axiom].instantiate(_map1)
        line2 = prover.add_instantiated_assumption(f_axiom,
                                                   ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                       axiom], _map1)

        quantifier = quantified_formula.root
        equivalent = Formula(quantifier, quantified_formula.variable,
                             conclusion)

        f1 = Formula('->', formula, equivalent)
        f2 = Formula('->', equivalent, formula)
        conclusion = Formula('&', f1, f2)
        _map2 = {'R': last_formula.first.first.substitute({
            quantified_formula.variable: Term.parse('_')}),
            'Q': last_formula.first.second.substitute({
                quantified_formula.variable: Term.parse('_')}),
            'x': quantified_formula.variable,
            'y': quantified_formula.variable}
        index = QUANTIFIER_AXIOM[quantified_formula.root]

        new_conclusion = ADDITIONAL_QUANTIFICATION_AXIOMS[
            index + 14].instantiate(_map2)
        line3 = prover.add_instantiated_assumption(new_conclusion,
                                                   ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                       index + 14], _map2)
        line4 = prover.add_mp(new_conclusion.second, line1, line3)
        line5 = prover.add_tautological_implication(conclusion, {line2,
                                                                 line4})

        return equivalent, prover.qed()

    else:
        f = Formula('->', formula, formula)
        conclusion = Formula('&', f, f)
        prover.add_tautology(conclusion)
        return formula, prover.qed()

def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    conclusion1, proof1 = \
        pull_out_quantifications_from_left_across_binary_operator(formula)
    line1 = prover.add_proof(proof1.lines[-1].formula, proof1)
    qunatifiers = list()
    variables = list()
    formula2 = conclusion1
    while not is_binary(formula2.root):
        qunatifiers.append(formula2.root)
        variables.append(formula2.variable)
        formula2 = formula2.predicate
    if len(qunatifiers) == 0:
        conclusion2, proof2 = \
            pull_out_quantifications_from_right_across_binary_operator(formula)
        line2 = prover.add_proof(proof2.lines[-1].formula, proof2)
        return conclusion2, prover.qed()
    conclusion2, proof2 = \
        pull_out_quantifications_from_right_across_binary_operator(
            formula2)
    last_line = proof2.lines[-1].formula
    line2 = prover.add_proof(proof2.lines[-1].formula, proof2)
    line4 = line2
    for i in range(len(qunatifiers)-1, -1, -1):
        _map = {'R': last_line.first.first.substitute({
           variables[i]: Term.parse('_')}),
            'Q': last_line.first.second.substitute({
                variables[i]: Term.parse('_')}),
            'x': variables[i],
            'y': variables[i]}
        if qunatifiers[i] == 'A':
            index = 14
        else:
            index = 15
        last_line = ADDITIONAL_QUANTIFICATION_AXIOMS[index].instantiate(_map)

        line3 = prover.add_instantiated_assumption(
            last_line, ADDITIONAL_QUANTIFICATION_AXIOMS[index], _map)
        line4 = prover.add_mp(last_line.second, line2, line3)
        line2 = line4
        last_line = last_line.second

    f1 = Formula('->', formula, last_line.first.second)
    f2 = Formula('->', last_line.first.second, formula)
    implication = Formula('&', f1, f2)
    prover.add_tautological_implication(implication, {line1, line4})
    return last_line.first.second, prover.qed()

def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    if is_unary(formula.root):
        formula1, proof1 = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        line1 = prover.add_proof(proof1.lines[-1].formula, proof1)
        f_neg = Formula('~', proof1.lines[-1].formula.first.second)
        f1 = Formula('->', formula, f_neg)
        f2 = Formula('->', f_neg, formula)
        f_negation = Formula('&', f1, f2)
        line2 = prover.add_tautology(Formula('->', proof1.lines[-1].formula,
                                             f_negation))
        line3 = prover.add_mp(f_negation, line1, line2)
        formula2, proof2 = pull_out_quantifications_across_negation(f_neg)
        line4 = prover.add_proof(proof2.lines[-1].formula, proof2)
        f1 = Formula('->', formula, formula2)
        f2 = Formula('->', formula2, formula)
        implication = Formula('&', f1, f2)
        line5 = prover.add_tautological_implication(implication, {line3,
                                                                  line4})

        return formula2, prover.qed()

    if is_binary(formula.root):
        formula1, proof1 = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        line1 = prover.add_proof(proof1.lines[-1].formula, proof1)
        formula2, proof2 = \
            to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        line2 = prover.add_proof(proof2.lines[-1].formula, proof2)
        new_formula = Formula(formula.root, formula1, formula2)
        f1 = Formula('->', formula, new_formula)
        f2 = Formula('->', new_formula, formula)
        f_last = Formula('&', f1, f2)
        line3 = prover.add_tautological_implication(f_last, {line1, line2})
        formula3, proof3 = pull_out_quantifications_across_binary_operator(new_formula)
        f1 = Formula('->', formula, formula3)
        f2 = Formula('->', formula3, formula)
        conclusion = Formula('&', f1, f2)
        line4 = prover.add_proof(proof3.lines[-1].formula, proof3)
        line5 = prover.add_tautological_implication(conclusion, {line3, line4})

        return formula3, prover.qed()

    elif is_quantifier(formula.root):
        formula1, proof1 = to_prenex_normal_form_from_uniquely_named_variables(
            formula.predicate)
        last_line = proof1.lines[-1].formula
        line1 = prover.add_proof(last_line, proof1)
        _map = {'R': last_line.first.first.substitute({
            formula.variable: Term.parse('_')}),
            'Q': last_line.first.second.substitute({
                formula.variable: Term.parse('_')}),
            'x': formula.variable,
            'y': formula.variable}

        index = QUANTIFIER_AXIOM[formula.root]

        new_conclusion = ADDITIONAL_QUANTIFICATION_AXIOMS[index + 14].instantiate(_map)
        line2 = prover.add_instantiated_assumption(new_conclusion,
                ADDITIONAL_QUANTIFICATION_AXIOMS[index + 14], _map)
        line3 = prover.add_mp(new_conclusion.second, line1, line2)
        return new_conclusion.second.first.second, prover.qed()

    else:
        f1 = Formula('->', formula, formula)
        implication = Formula('&', f1, f1)
        line1 = prover.add_tautology(implication)
        return formula, prover.qed()


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    f1, p1 = uniquely_rename_quantified_variables(formula)
    line1 = prover.add_proof(p1.lines[-1].formula, p1)
    f2, p2 = to_prenex_normal_form_from_uniquely_named_variables(f1)
    line2 = prover.add_proof(p2.lines[-1].formula, p2)

    formula1 = Formula('->', formula, f2)
    formula2 = Formula('->', f2, formula)
    conclusion = Formula('&', formula1, formula2)
    line3 = prover.add_tautological_implication(conclusion, {line1, line2})

    return conclusion.first.second, prover.qed()
