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
            # new_relation contain relation which aren't original function
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
    if is_function(term.root):
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
        lst_to_return.append(Formula('=',func_arg_tuple))
        return lst_to_return

    # else
    return [Formula(term.root, {})]


"""
Helper for 8.4,
relation and equality are the same, except for the final_conclusion
(which is almost the same)
"""
def handle_relation_and_equality(formula , lst, final_conclusion, first = False):
    # base case
    if len(lst) == 1:
        arg = (lst[0].arguments[0],) + lst[0].arguments[1].arguments
        for _t in arg:
            assert type(_t) == Term
        form = Formula(function_name_to_relation_name(lst[0].arguments[1].root),
                            arg)
        return Formula('A', lst[0].arguments[0].root, Formula('->', form, final_conclusion))

    if first:
        arg = (lst[0].arguments[0] , ) + lst[0].arguments[1].arguments
        for _t in arg:
            assert type(_t) == Term
        form = Formula('->', Formula(function_name_to_relation_name(lst[0].arguments[1].root),
                                     arg),
                       handle_relation_and_equality(formula, lst[1:], final_conclusion))

        d = Formula('A', lst[0].arguments[0].root, form)
        return d
    else:
        arg = ((lst[0].arguments[0]),) + lst[0].arguments[1].arguments
        for _t in arg:
            assert type(_t) == Term
        form_left = Formula(function_name_to_relation_name(lst[0].arguments[1].root),
                            arg)
        return Formula('A', lst[0].arguments[0].root,
                       Formula('->', form_left ,handle_relation_and_equality(formula, lst[1:], final_conclusion)))

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
    # s1 = Formula.parse("R(f(g(x)),h(2,y),3)")
    # # g = Formula.parse("Az1[(G(z1,x->Az2[(F(z2,z1->Az3[(H(z3,2,y->R(z2, z3, 3))])])]")
    g2 = Formula.parse("Ax[Ay[Az[((F(z1)->G(z2])->H(z3))]->GT(y,4))")

    # # for arg in lst:
    # A1 = Formula.parse("R(f(c),g(h(a),b))")
    # A2 = compile_term(Term.parse("f(c)"))
    # A3 = compile_term(Term.parse("g(h(a),b))"))
    # A5 = Formula.parse("Az1[(F(z1,c)->Az2[(H(z2,a)->Az3[G(z3,z2,b])])]")


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
        h = Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))
        return h


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
