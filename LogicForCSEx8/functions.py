# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *

def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    # model's universe and Constant Meanings stays the same
    new_relation_meanings = {}

    # adding all the current relation meaning of the model
    for r_meaning_key, r_meaning_val in model.relation_meanings.items():
        new_relation_meanings[r_meaning_key] = r_meaning_val

    # func = func name
    # input_and_output = dict that contains the arg that the function gets as
    #                    key (of dict),
    #                    and the output of the function with the above arg as
    #                    value (of dict)
    for func, input_and_output in model.function_meanings.items():
        new_meaning = set()
        # merging the input and output of the function to one tuple, where the
        # first item is the output of the function, and the next items are
        # the arguments(input) of the function
        for _input,_output in input_and_output.items():
            new_tuple = (_output, )
            for _in in _input:
                new_tuple = new_tuple + tuple(_in)
            new_meaning.add(new_tuple)
        new_relation_meanings[function_name_to_relation_name(func)] = new_meaning
    return Model(model.universe, model.constant_meanings, new_relation_meanings,{})


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2
    # faulty model = function for same input return different answers
    new_func_meanings = {}
    new_relation = {}
    # model_original_functions contains the name of relation that need to be
    # converted back to function
    model_original_functions = set()
    for func_name in original_functions:
        model_original_functions.add(function_name_to_relation_name(func_name))
    for _name, _arg in model.relation_meanings.items():
        if _name not in model_original_functions:
            # new_relation contains relations which aren't originally functions
            new_relation[_name] = model.relation_meanings[_name]
            continue
        func_input_and_output = {}
        for _tuple in _arg:
            # case where for same input, function return different solution
            if _tuple[1:] in func_input_and_output and\
                            func_input_and_output[_tuple[1:]] != _tuple[0]:
                return None
            # else
            func_input_and_output[_tuple[1:]] = _tuple[0]
        new_func_meanings[relation_name_to_function_name(_name)] =\
                                                    func_input_and_output
    # checking that the function gets all model arguments, and not partial,
    for func_name,input_and_output in new_func_meanings.items():
        # arity - number of arguments that the function gets
        arity = len(next(iter(input_and_output.keys())))
        # need to be len(model.universe) ** arity number of input and output
        # in the model
        if len(input_and_output) != len(model.universe) ** arity:
            return None

    return Model(model.universe, model.constant_meanings, new_relation, new_func_meanings)



def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3
    lst_to_return = list()
    # f(x,h(y)) --> f(x,z1) --> [z1=h(y), z2=f(x,z1)]
    func_arg_tuple = tuple()
    for arg in term.arguments:
        if is_function(arg.root):
            _compiled_term = compile_term(arg)
            for _formula in _compiled_term:
                if _formula.arguments[0].root[0] == 'z':
                    lst_to_return.append(_formula)
            # last formula contain the name of the function,
            # e.g, z1 = func(), and we need the z1
            func_arg_tuple = func_arg_tuple +\
                             (Term(_compiled_term.pop().arguments[0].root),)
        else:
            # if its not function, it stays as is.
            func_arg_tuple = func_arg_tuple + (arg,)
    func_arg_tuple = (Term(next(fresh_variable_name_generator)), ) +\
                     (Term(term.root, func_arg_tuple), )
    lst_to_return.append(Formula('=', func_arg_tuple))
    return lst_to_return


"""
Helper for 8.4,
relation and equality are the same, except for the final_conclusion
(which is almost the same)
"""
def handle_relation_and_equality(formula , lst_of_z, final_conclusion, first = False):
    # base case
    if len(lst_of_z) == 1:

        arg = (lst_of_z[0].arguments[0],) + lst_of_z[0].arguments[1].arguments
        # for _t in arg:
        #     assert type(_t) == Term
        form = Formula(function_name_to_relation_name(lst_of_z[0].arguments[1].root),
                            arg)
        return Formula('A', lst_of_z[0].arguments[0].root, Formula('->', form,final_conclusion))

    if first:
        if len(lst_of_z) == 0:
            return formula

        arg = (lst_of_z[0].arguments[0] , ) + lst_of_z[0].arguments[1].arguments
        # for _t in arg:
        #     assert type(_t) == Term
        form = Formula('->', Formula(function_name_to_relation_name(lst_of_z[0].arguments[1].root),
                                     arg),
                       handle_relation_and_equality(formula, lst_of_z[1:], final_conclusion))

        return Formula('A', lst_of_z[0].arguments[0].root, form)
    else:

        arg = ((lst_of_z[0].arguments[0]),) + lst_of_z[0].arguments[1].arguments
        # for _t in arg:
        #     assert type(_t) == Term
        form_left = Formula(function_name_to_relation_name(lst_of_z[0].arguments[1].root),
                            arg)
        return Formula('A', lst_of_z[0].arguments[0].root,
                       Formula('->', form_left ,
                               handle_relation_and_equality(formula, lst_of_z[1:], final_conclusion)))

def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4

    if is_relation(formula.root) or is_equality(formula.root):
        lst_of_z = list()  # all the z(i) = something
        final_relation_arguments = list()
        for arg in formula.arguments:
            if is_function(arg.root):
                # final_relation_arguments.append(compile_term(arg)[-1].arguments[0]) same as two line forward
                for _term in compile_term(arg):
                    lst_of_z.append(_term)
                final_relation_arguments.append(lst_of_z[-1].arguments[0])
            else:
                final_relation_arguments.append(arg)
        final_arg = list()
        # creating the final result (the last '->')
        for arg in final_relation_arguments:
            if is_equality(arg.root):
                final_arg.append(arg.arguments[0])
            else:
                final_arg.append(arg)

        if is_relation(formula.root):
            final_relation = Formula(formula.root, final_arg)
            return handle_relation_and_equality(formula, lst_of_z, final_relation, True)

        else:
            assert is_equality(formula.root)
            final_equality = Formula(formula.root, final_arg)
            return handle_relation_and_equality(formula, lst_of_z, final_equality, True)

    elif is_unary(formula.root):
        return Formula('~',replace_functions_with_relations_in_formula(formula.first))

    elif is_binary(formula.root):
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula(formula.first),
                       replace_functions_with_relations_in_formula(formula.second))
    else:
        assert is_quantifier(formula.root)
        return Formula(formula.root, formula.variable,
                    replace_functions_with_relations_in_formula(formula.predicate))


def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    new_formulas = set()
    for formula in formulas:
        if not is_relation(formula.root):
            new_formulas.add(formula)
        else:
            new_formula = replace_functions_with_relations_in_formula(formula)
            new_formulas.add(new_formula)
            v1 = "z1"
            v2 = "z2"
            t1 = Term(v1)
            t2 = Term(v2)
            temp = new_formula
            while is_quantifier(temp.root):
                i = 3
                # zi will be a name of the function's variable
                temp = temp.predicate
                arguments = temp.first.arguments
                new_arguments = list()
                new_arguments.append(arguments[0])
                for j in range(len(arguments[1:])):
                    new_arguments.append(Term("z"+str(i)))
                    i += 1
                relation = Formula(temp.first.root, tuple(new_arguments))
                r1 = Formula(relation.root, (t1,) + relation.arguments[1:])
                r2 = Formula(relation.root, (t2,) + relation.arguments[1:])
                f1 = Formula('E', arguments[0].root, relation)
                f2_second = Formula('=', (t1, t2))
                f2_first = Formula('&', r1, r2)
                f2 = Formula('->', f2_first, f2_second)
                f2 = Formula('A', v2, f2)
                f2 = Formula('A', v1, f2)
                # f1 and f2 are ready to be added each variable before them

                for arg in relation.arguments[1:]:
                    f1 = Formula('A', arg.root, f1)
                    f2 = Formula('A', arg.root, f2)

                new_formulas.add(f1)
                new_formulas.add(f2)
                temp = temp.second

    return new_formulas



def replace_equality_with_SAME_in_formula(formula:Formula) -> Formula:
    """
    Replaces a single formula's equalities with SAME relation
    :param formula: Formula
    :return: the formula with all equalities changed to SAME relations
    """
    if is_equality(formula.root):
        return Formula("SAME", formula.arguments)
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_equality_with_SAME_in_formula(
            formula.predicate))
    if is_binary(formula.root):
        return Formula(formula.root, replace_equality_with_SAME_in_formula(
            formula.first), replace_equality_with_SAME_in_formula(
            formula.second))
    if is_unary(formula.root):
        return Formula(formula.root, replace_equality_with_SAME_in_formula(
            formula.first))
    else:  # relation
        return formula


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6
    relations = set()
    new_formulas = set()
    for formula in formulas:
        new_formulas.add(replace_equality_with_SAME_in_formula(formula))
        relations = formula.relations()

    SAME_XY = Formula('->', Formula('SAME', (Term('x'),Term('y'))),
                      Formula('SAME', (Term('y'),Term('x'))))
    SAME_XYZ = Formula('->', Formula('&', Formula('SAME', (Term('x'), Term('y'))),
                                     Formula('SAME', (Term('y'), Term('z')))),
                       Formula('SAME', (Term('x'), Term('z'))))
    SAME_XX = Formula('SAME', (Term('x'), Term('x')))
    # reflexivity
    new_formulas.add(Formula('A', "x", SAME_XX))
    # symmetry
    new_formulas.add(Formula('A', "y", Formula('A', "x", SAME_XY)))
    # transitivity
    new_formulas.add(Formula('A', "z", Formula('A', "y", Formula('A', "x",
                                                           SAME_XYZ))))
    relations = list(relations)
    for relation in relations:
        args1 = list(); args2 = list()
        same = None
        for i in range(relation[1]):
            xi = Term("x"+str(i+1))
            yi = Term("y"+str(i+1))
            args1.append(xi)
            args2.append(yi)
            same_xi_yi = Formula('SAME', (xi, yi))
            if same is not None:
                same = Formula('&', same, same_xi_yi)
            else:
                same = same_xi_yi
        relation_formula = Formula('->', Formula(relation[0], args1),
                                   Formula(relation[0], args2))
        # same (x1,...,xn), (y1,...,yn) -> relation(x1,...,xn) -> relation(y1,...,yn)
        relation_formula = Formula('->', same, relation_formula)
        # add quantifiers
        for i in range(relation[1]):
            relation_formula = Formula('A', "x"+str(i+1), relation_formula)
        for i in range(relation[1]):
            relation_formula = Formula('A', "y"+str(i+1), relation_formula)
        new_formulas.add(relation_formula)
    return new_formulas


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    relation_meanings = dict(model.relation_meanings)
    same_set = set()
    # add tuples of the same elements in the universe
    for element in model.universe:
        same_set.add((element, element))
    relation_meanings['SAME'] = same_set

    return Model(model.universe, model.constant_meanings, relation_meanings,
                 model.function_meanings)

def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
    seen = dict()
    # seen[element] = element in the equal_dict that is the same
    equal_dict = dict()
    # equal_dict keeps keys and the elements that share their same value
    for equality in model.relation_meanings['SAME']:
        if equality[0] != equality[1]:
            # not x=x
            if equality[0] not in seen.keys():
                if equality[1] not in seen.keys():
                    # both elements of equality weren't seen yet
                    equal_dict[equality[0]] = set()
                    equal_dict[equality[0]].add(equality[0])
                    equal_dict[equality[0]].add(equality[1])
                    seen[equality[0]] = equality[0]
                    seen[equality[1]] = equality[0]
                else:
                    # equality[1] in seen keys
                    equal_dict[seen[equality[1]]].add(equality[0])
                    seen[equality[0]] = seen[equality[1]]
            else:
                # equality[0] in seen keys
                if equality[1] not in seen.keys():
                    # equality[1] not in seen keys
                    equal_dict[seen[equality[0]]].add(equality[1])
                    seen[equality[1]] = seen[equality[0]]
                else:
                    # equality[0] and equality[1] in seen keys
                    if seen[equality[0]] == seen[equality[1]]:
                        continue
                    else:
                        set2 = equal_dict.pop(seen[equality[1]])
                        equal_dict[seen[equality[0]]].update(set2)
                        seen[equality[1]] = equality[0]
        else:
            if equality[0] not in seen.keys():
                equal_dict[equality[0]] = set()
                equal_dict[equality[0]].add(equality[0])
                seen[equality[0]] = equality[0]

    constant_meanings = dict(model.constant_meanings)
    for constant in constant_meanings.keys():
        # change each constant's value to identifier's value
        constant_meanings[constant] = seen[constant_meanings[constant]]

    relation_meanings = dict()
    for relation in model.relation_meanings.keys():
        if relation != 'SAME':
            new_tuples = set()
            relation_set = set(model.relation_meanings[relation])
            while len(relation_set):
                current_tuple = relation_set.pop()
                new_tuple = list()
                # change each tuple, every element will belong to identifiers
                for element in current_tuple:
                    new_tuple.append(seen[element])
                new_tuples.add(tuple(new_tuple))
            relation_meanings[relation] = new_tuples

    return Model(equal_dict.keys(), constant_meanings, relation_meanings)
