# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/completeness.py

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *

def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants

def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)

def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation, is one of
        the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1
    _all_constant = set() # all the constant of all the formulas in sentences
    _all_relation = set() # contain all the relation names and it arity
    for _s in sentences:
        _all_constant = _all_constant.union(_s.constants())
        _all_relation = _all_relation.union(_s.relations())

    # for each relation checking if all the possibility of
    # the relation : 'relation_name(any possible combination from constant)'
    # or 'relation_name(any possible combination from constant)' in the
    # sentences, if not, return False (this is the def of primitively_closed)
    for _relation in _all_relation:
        for _arg in list(itertools.product(_all_constant,
                                           repeat=_relation[1])):
            # _relation[0] = relation name,
            # _relation[1] = the number of argument of this relation (arity)
            form = Formula(_relation[0], [Term(i) for i in _arg])
            if form not in sentences and Formula('~', form) not in sentences:
                return False

    return True

def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.2
    _all_constant = set() # all the constant of all the formulas in sentences
    _all_relevant_formula = set() # contain all formula of the form: Ax[something]
    for _s in sentences:
        _all_constant = _all_constant.union(_s.constants())
        if _s.root == 'A':
            _all_relevant_formula.add(_s)

    # replace the variable of the quantification with every const in the sentence,
    # and than checking, if the predicate with that replacement is in the sentence
    for _form in _all_relevant_formula:
        for _const in _all_constant:
            if _form.predicate.substitute({_form.variable : Term(_const)}) \
                    not in sentences:
                return False
    return True



def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3
    _all_constant = set()  # all the constant of all the formulas in sentences
    _all_relevant_formula = set()  # contain all formula of the form: Ex[something]
    for _s in sentences:
        _all_constant = _all_constant.union(_s.constants())
        if _s.root == 'E':
            _all_relevant_formula.add(_s)

    for _form in _all_relevant_formula:
        # replace the variable of the quantification with every const in the sentence,
        # and than checking, if the predicate with that replacement is in the sentence
        # if exist at least one of such replacement in sentence, than return True
        # 'not_exist', represent if for each formula
        # (predicate of relevant formula) exist such formula in sentence or not
        not_exist = True
        for _const in _all_constant:
            if _form.predicate.substitute({_form.variable : Term(_const)}) \
                    in sentences:
                not_exist = False
                break
        if not_exist:
            return False
    return True


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2

    # wanting a quantifier-free sentence, and if unsatisfied is so,
    # we can return it
    if not is_quantifier(unsatisfied.root):
        return unsatisfied

    # else:
    for _const in model.universe:
        # peel of the Ax[] -->[] and replacing x with const
        substituted_instance = unsatisfied.predicate.substitute(
            {unsatisfied.variable: Term(_const)})
        # we search for formula that not satisfied by the given model
        if model.evaluate_formula(substituted_instance):
            continue
        # if unsatisfied.root == 'A' we would like to peel the 'A' OFF because
        # wanting a quantifier-free sentence
        elif unsatisfied.root == 'A' or substituted_instance in sentences:
            return find_unsatisfied_quantifier_free_sentence(sentences, model,
                                                      substituted_instance)


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1
    set_to_return = set()
    if is_relation(quantifier_free.root):
        return {quantifier_free}
    elif is_unary(quantifier_free.root):
        set_to_return = get_primitives(quantifier_free.first)
    elif is_binary(quantifier_free.root):
        set_to_return = set_to_return.union(set_to_return,
                                            get_primitives(quantifier_free.first),
                                            get_primitives(quantifier_free.second))
    return set_to_return

def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """    
    assert is_closed(sentences)
    # Task 12.3.2
    # as per guidance, first construct the Model
    _universe = get_constants(sentences)
    _constant_meanings = {const : const for const in _universe}
    _relation_meanings = dict()
    # ignoring any sentence in sentences that is not a primitive sentence
    # or its negation while constructing this model
    for _s in sentences:
        if is_relation(_s.root):
            if _s.root not in _relation_meanings:
                _relation_meanings[_s.root] =  {tuple(str(arg) for arg in _s.arguments)}
            else:
                # if already exist, adding another tuple with this arguments
                _relation_meanings[_s.root].update({tuple(str(arg) for arg in _s.arguments)})
    _model = Model(_universe, _constant_meanings, _relation_meanings)

    # as per guidance, 'If this model satisfies sentences, then you are done'
    # _unsatisfied = 'Otherwise, find some sentence from sentences that
    #                 this model does not satisfy'
    _unsatisfied = Formula
    found_unsatisfied = False
    for _sentence in sentences:
        if not _model.evaluate_formula(_sentence):
            found_unsatisfied = True
            _unsatisfied = _sentence
            break
    if not found_unsatisfied:
        return _model

    # finding quantifier free unsatisfied sentence
    quantifier_free_unsatisfied_sentence = _unsatisfied
    if is_quantifier(_unsatisfied.root):
        quantifier_free_unsatisfied_sentence =\
            find_unsatisfied_quantifier_free_sentence(sentences, _model, _unsatisfied)

    prover = Prover(sentences | Prover.AXIOMS | {quantifier_free_unsatisfied_sentence})

    all_lines = set()
    line1 = prover.add_assumption(quantifier_free_unsatisfied_sentence)

    for _primitive in get_primitives(quantifier_free_unsatisfied_sentence):
        if _primitive in sentences:
            all_lines.add(prover.add_assumption(_primitive))
        else:
            all_lines.add(prover.add_assumption(Formula('~', _primitive)))
    line2 = prover.add_tautological_implication(Formula('~', quantifier_free_unsatisfied_sentence), all_lines)
    # ~quantifier_free_unsatisfied_sentence&quantifier_free_unsatisfied_sentence
    form = Formula('&',
                   Formula('~', quantifier_free_unsatisfied_sentence),
                   quantifier_free_unsatisfied_sentence)
    prover.add_tautological_implication(form, {line1, line2})
    return prover.qed()




def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6

def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: a valid proof.
        constant: a constant name that does not appear as a template constant
            name in any of the assumptions of the given proof.
        variable: a variable name that does not appear anywhere in given the
            proof or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1

def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2

def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
