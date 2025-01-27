# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
from propositions.operators import *
from propositions.axiomatic_systems import *

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    list_var_in_model_ordered = list(model.keys())
    # by default ordered alphabetic
    list_var_in_model_ordered.sort()

    to_return = list()
    for var in list_var_in_model_ordered:
        if model[var] is True:
            to_return.append(Formula(var))
        else:
            to_return.append(Formula('~', Formula(var)))
    return to_return


def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b
    all_lines = list()

    # CASE 1 : handle case as x where x is variable
    if is_variable(str(formula)):
        if evaluate(formula, model):
            # if the var evaluate to True in the model
            all_lines.append(Proof.Line(formula))
            statement = InferenceRule(formulae_capturing_model(model), formula)
            return Proof(statement, AXIOMATIC_SYSTEM, all_lines)
        else:
            # if the var evaluate to False in the model
            all_lines.append(Proof.Line(Formula('~',formula)))
        statement = InferenceRule(formulae_capturing_model(model), Formula('~',formula))
        return Proof(statement, AXIOMATIC_SYSTEM, all_lines)

    # CASE 2 : (p->q):
    elif formula.root == '->':
        # formula p->q evaluate to True in the given model
        if evaluate(formula, model):
            # there are 2 cases : or p evaluate to False, or q eval to True
            if not evaluate(formula.first, model):
                # case where p eval to False
                # proof1 is proof of 'p'
                proof1 = prove_in_model(Formula('~', formula.first), model)
                # using I2
                return prove_corollary(proof1, formula, I2)
            else:
                # case where q eval to True
                proof1 = prove_in_model(formula.second, model)
                return prove_corollary(proof1, formula, I1)

        # formula f = (p->q) evaluate to False in the given model
        # therefor p eval to True and q eval to False
        # than we want to prove ~f = ~(p->q) , NI does exactly that.
        # NI = (p->(~q->~(p->q)))
        else:
            prove_p = prove_in_model(formula.first, model)
            prove_not_q = prove_in_model(Formula('~',formula.second), model)
            # ~f = ~(p->q) = Formula('~', formula)
            combined = combine_proofs(prove_p, prove_not_q, Formula('~', formula), NI)
            return combined
    # case 3
    else:
        # must be f = ~g
        assert (formula.root == '~')
        if evaluate(formula, model):
            # if f is True than ~g = True ---> g = False
            return prove_in_model(formula.first, model)
        else:
            # if f is False than ~g is False --> g = True
            # prove g, than using NN we would get ~~g, which is ~f -> True
            prove_g = prove_in_model(formula.first, model)
            # from g, using NN we prove ~~g = ~formula = ~f
            return prove_corollary(prove_g, Formula('~', formula), NN)

    # return Proof(statement, AXIOMATIC_SYSTEM, all_lines)

def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    # copying the same rules in addition to MP, I0, I1, D, R
    all_rules = set()
    for rule in proof_from_affirmation.rules:
        all_rules.add(rule)
    for rule in [MP, I0, I1, D, R]:
        all_rules.add(rule)

    # proof of (p->(q->(q->p)))
    proof_affirmation_remove_last_assumption =\
        remove_assumption(proof_from_affirmation)

    # proof of (p->(~q->(q->p))) from the example
    proof_negation_remove_last_assumption =\
        remove_assumption(proof_from_negation)

    # using D, and both of the above proofs, we can prove the conclusion
    #  without the last assumption
    combined_proof = combine_proofs(proof_affirmation_remove_last_assumption,
                                    proof_negation_remove_last_assumption,
                          proof_from_affirmation.statement.conclusion, R)

    return Proof(combined_proof.statement, all_rules, combined_proof.lines)




def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a

    statement = InferenceRule(formulae_capturing_model(model), tautology)

    # rules are AXIOMATIC_SYSTEM
    list_of_var_in_formula = list(tautology.variables())
    list_of_var_in_formula.sort()
    for var in list_of_var_in_formula:
        if var not in model:
            new_model = dict(model)
            new_model[var] = True
            # proof 1 is with that var with value True
            proof1 = prove_tautology(tautology, new_model)
            new_model[var] = False
            # proof 2 is with that var with value False
            proof2 = prove_tautology(tautology, new_model)
            # proof without that var
            return reduce_assumption(proof1, proof2)

    # if the model contains all the var in the tautology formula
    return prove_in_model(tautology, model)

def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    if is_tautology(formula):
        # if it tautology, return a proof
        return prove_tautology(formula, {})
    else:
        # if its not tautology, than there must be a model which the formula
        # doesn't hold upon.
        # iterating over all model, till finding model which the formula
        # doesn't hold upon.
        for model in all_models(list(formula.variables())):
            if not evaluate(formula, model):
                return model

# lst is a union of assumptions and conclusion
# this function returning the formula encode
# meaning : (p1->(p2->(p3->(p4->q))))
def encode_helper(lst):
    if len(lst) > 1:
        return Formula('->', lst[0], encode_helper(lst[1:]))
    return lst[0]

def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    union_assumptions_conclusion = list()
    for assumption in rule.assumptions:
        union_assumptions_conclusion.append(assumption)
    union_assumptions_conclusion.append(rule.conclusion)

    return encode_helper(union_assumptions_conclusion)


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    # rules AXIOMATIC_SYSTEM
    statement  = rule
    encoded_formula = encode_as_formula(rule) # = (p1->(p2->(p3->(p4->q))))
    # all lines = proof where the last line is : (p1->(p2->(p3->(p4->q))))
    all_lines = list(prove_tautology(encode_as_formula(rule), {}).lines)
    # using MP number of times and len(assumption) would get us q
    # running on assumption p1 and than p2, ....p4
    for assumption in rule.assumptions:
        # for example, all_line.add(p1)
        all_lines.append(Proof.Line(assumption))
        # adding to all_lines (p2->(p3->(p4->q))) (proven by MP and the
        # last 2 lines)
        # and update the encoded_formula to it
        encoded_formula = encoded_formula.second # (p2->(p3->(p4->q)))
        all_lines.append(Proof.Line(encoded_formula, MP,
                                    [len(all_lines) - 1, len(all_lines) - 2]))

        # it would look like:
        # Line n :      (p1->(p2->(p3->(p4->q))))
        # Line n + 1 :  p1
        # Line n+2   :  (p2->(p3->(p4->q)) (MP on the last two lines)
        # Line n+3   :  q2
        # Line n+4   :  (p3->(p4->q)
        # Line n+5   :  p3  and so on, till q is proved.

    return Proof(statement, AXIOMATIC_SYSTEM, all_lines)



def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5

    # all_var - union of all the variables in all of the formulas
    all_var = set()
    for form in formulae:
        for var in form.variables():
            all_var.add(var)

    for model in all_models(list(all_var)):
        for idx,form in enumerate(formulae):
            if not evaluate(form, model):
                break
            # if got to the last formula, and it evaluate to true as well,
            # than on this model all formula holds
            if idx == len(formulae) - 1:
                return model
    # if got here, than there isn't a model on which all formula holds
    # therefor, from False we can prove anything, even false things.
    # therefor prove_sound_inference would give us a proof for False thing
    # (because the assumption are False for every model)
    # F -> anything even False
    return prove_sound_inference(InferenceRule(formulae, Formula.parse("~(p->p)")))

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
