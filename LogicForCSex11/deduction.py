# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False, proof_contradiction = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    # the new set of assumption is : (same without the given 'assumption' arg)
    assumption_without_last = set()
    for _schema in proof.assumptions:
        if _schema.formula != assumption:
            assumption_without_last.add(_schema)

    # creating a prover
    proof_to_return = Prover(assumption_without_last)

    # dictionary that represent the index of the old line in the new proof,
    # for example if the old line contain f, than the new line will contain
    # assumption->f and dict[old_idx] = new_idx
    old_line_to_new_line_idx = dict()

    for idx, line in enumerate(proof.lines):
        # we want to prove that 'p->proof.conclusion' where p is the assumption

        # in each iteration we want to add assumption->old_line
        _conclusion = Formula('->', assumption, line.formula)
        if type(line) == Proof.TautologyLine:
            old_line_to_new_line_idx[idx] = \
                proof_to_return.add_tautology(_conclusion)

        elif type(line) == Proof.AssumptionLine:
            # case where the line is the assumption we removed from assumption
            # (the given assumption in the arguments of the function)
            if line.formula == assumption:
                # adding p->p
                old_line_to_new_line_idx[idx] = \
                    proof_to_return.add_tautology(Formula('->', line.formula,
                                                          line.formula))
            else:
                # adding q
                antecedent_line = proof_to_return.add_instantiated_assumption(
                    line.formula, line.assumption, line.instantiation_map)
                # adding q->(p->q)
                conditional_line = proof_to_return.add_tautology(Formula('->', line.formula,
                                                      _conclusion))
                # adding (p->q)
                old_line_to_new_line_idx[idx] = proof_to_return.add_mp(
                    _conclusion, antecedent_line,conditional_line)

        elif type(line) == Proof.MPLine:
            # line1 = antecedent_line_number, line2 = conditional_line_number
            line1 = old_line_to_new_line_idx[line.antecedent_line_number]
            line2 = old_line_to_new_line_idx[line.conditional_line_number]
            old_line_to_new_line_idx[idx] = \
                proof_to_return.add_tautological_implication(_conclusion,
                                                             {line1, line2})
        else:
            assert(type(line) == Proof.UGLine)
            predicate_line_number = old_line_to_new_line_idx[
                                                    line.predicate_line_number]
            # predicate_line_number contain the line such 'p->f'
            # wanting to proof p->Ax[f(x)]
            # current line is : Ax[f(x)]
            # Ax[p->f]
            already_converted_predicate = proof_to_return._lines[predicate_line_number].formula # p->f
            _formula = Formula('A', line.formula.variable, already_converted_predicate) #Ax[p->f]

            # ug_line = Ax(p->f)
            ug_line = proof_to_return.add_ug(_formula, predicate_line_number)

            _map = {'Q' : assumption,
                    'R' : line.formula.predicate.substitute(
                        {line.formula.variable: Term('_')}),
                    'x' : line.formula.variable}
            _formula_US = Formula('->', _formula, _conclusion)
            conditional_line = proof_to_return.add_instantiated_assumption(
                                                _formula_US, Prover.US, _map)
            old_line_to_new_line_idx[idx] = proof_to_return.add_mp(
                                        _conclusion, ug_line, conditional_line)
            
    # using this for task 11.2, proof_by_way_of_contradiction
    if proof_contradiction:
        _conclusion = Formula('~', assumption)
        last_line = len(proof_to_return._lines) - 1
        proof_to_return.add_tautological_implication(_conclusion, {last_line})

    return proof_to_return.qed()


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2

    return remove_assumption(proof, assumption, False, True)