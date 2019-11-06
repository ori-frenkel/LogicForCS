# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, List, Mapping

import itertools

from propositions.syntax import *
from propositions.proofs import *

Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()
"""
handle the case that we need to evaluate (X binary_operation Y)
"""
def evaluate_binary_operation_handler(formula: Formula, model: Model) -> bool:
    first = evaluate(formula.first, model) # the X
    second = evaluate(formula.second, model) # the Y
    if formula.root == '&':
        if first is False or second is False:
            return False
        return True
    elif formula.root == '|':
        if first is True or second is True:
            return True
        return False
    else:  # must be '->'
        # there are 2 cases where '->' return true
        # 1. False -> True/False
        # 2. True -> True
        assert (formula.root == '->')
        if first is False or second is True:
            return True
        return False

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_constant(formula.root):
        if formula.root == 'T':
            return True
        return False # if its not 'T' than it must be 'F'
    elif is_variable(formula.root):
        return model.get(formula.root)
    else:
        # if we got here, than it must be binary operation
        assert(is_binary(formula.root))
        return evaluate_binary_operation_handler(formula, model)


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    # for v in variables:
    #     assert is_variable(v)
    # Task 2.2

    to_return_lst = list()
    to_return = itertools.product((False, True), repeat=len(variables))
    for possibility in to_return:
        my_dict = {}
        for index,var in enumerate(variables):
            my_dict.update({var : possibility[index]})
        to_return_lst.append(my_dict.copy())
        # print(my_dict)
        my_dict.clear()
    # print(to_return_lst)
    return to_return_lst





def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    # all_models_local = all_models(list(formula.variables()))
    to_return = list()
    for l_model in models:
        to_return.append(evaluate(formula, l_model))
    return to_return

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    """
    headers = list()
    table = list()
    result_lst = list()
    index = 0
    all_models_local = all_models(list(formula.variables()))
    for result in truth_values(formula, all_models_local):
        if result:
            result_lst.append("T")
        else:
            result_lst.append("F")
    
    temp_lst = list()
    for mod_dict in all_models_local:
        for var in headers:
            if mod_dict.get(var):
                temp_lst.append("T")
            else:
                temp_lst.append("F")
        # adding the content of result
        temp_lst.append(result_lst[index])
        index += 1
        table.append(temp_lst.copy())
        temp_lst.clear()
    from pip._internal.commands.list import tabulate

    for var in list(formula.variables()):
        headers.append(var)
    headers.append(str(formula)) # the result
    headers = sorted(headers)
    print(tabulate(table, headers, tablefmt="github"))
    """

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # A Formula is said to be a tautology if it gets the value True
    # in all models.
    # Task 2.5a
    all_models_local = all_models(list(formula.variables()))
    for bool_val in truth_values(formula, all_models_local):
        if not bool_val:
            return False
    return True

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    return not is_satisfiable(formula)

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # satisfiable -  if it gets the value True at least once
    # Task 2.5c
    all_models_local = all_models(list(formula.variables()))
    for bool_val in truth_values(formula, all_models_local):
        if bool_val:
            return True
    return False

def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    # the idea is -> first step put the var or ~var
    # than each time do - > add '(' at first
    # '(' + the_string '&' + the_new_string + ')'
    """
    We solve this equestion by using CNF.
    every var that is false we doing ~var, and connecting all the var by '&'
    and this will provide us with formula which is true just 
    for the given model
    """
    assert is_model(model)
    # Task 2.6
    first = True
    str_formula = ""
    for key,value in model.items():
        if first:
            first = False
            if not value:
                str_formula += '~'
            str_formula += key
        else:
            str_formula = "(" + str_formula + "&"
            if not value:
                str_formula += '~'
            str_formula += key
            str_formula += ")"
    # creating a list, that list[0] contain the string, because that what
    # list_to_string function is required
    list_of_string = list()
    list_of_string.append(str_formula)
    return str_to_form(list_of_string)

def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    first = True
    final_formula = ""
    formula_local = ""
    for model in all_models(variables):
        if not first:
            final_formula = "(" + final_formula + "|"
        for bool_result in values:
            formula_local = str(synthesize_for_model(model))
            if not bool_result:
                formula_local = "~" + formula_local
        final_formula += formula_local
        if not first:
            final_formula += ")"

    # creating a list, that list[0] contain the string, because that what
    # list_to_string function is required
    list_of_string = list()
    list_of_string.append(final_formula)
    return str_to_form(list_of_string)


# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
