# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax.py

"""Syntactic handling of first-order formulas and terms."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context."""

    def __init__(self, variable_name: str) -> None:
        """Initializes a `ForbiddenVariableError` from its offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it was to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd'))
             and s.isalnum()) or s == '_'

# any number or char
def is_alphanumeric(_str : str):
    for char in _str:
        if not (char.isalpha() or char.isdigit()):
            return False
    return True

def is_variable(s: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def is_function(s: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

"""
Helper function for task 9.1
get a term, and return True if term contain illegal variable,
raise exception otherwise
"""
def check_if_term_contain_illegal_var(_term : Term,
                                      forbidden_variables: AbstractSet[str]
                                      = frozenset()):

    # if its function, check all the arguments of the function
    if is_function(_term.root):
        for _arg in _term.arguments:
            check_if_term_contain_illegal_var(_arg, forbidden_variables)
    else:
        if _term.root in forbidden_variables:
            raise ForbiddenVariableError(_term.root)
    return True
@frozen
class Term:
    """An immutable first-order term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str,
                 arguments: Optional[Sequence[Term]] = None) -> None:
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        final_str = ""
        if is_function(self.root):
            final_str += self.root
            final_str += "("
            try:
                for idx, term in enumerate(self.arguments):
                    final_str += str(term)
                    # avoid situation like f(a,) - meaning
                    # if its the last arg, dont add ','
                    if idx != len(self.arguments) - 1:
                        final_str += ","
                return final_str + ")"
            except AttributeError:
                pass
        else:
            return self.root

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1
        # constant name '_'
        if s[0] == '_':
            return Term('_'), s[1:]
        if is_constant(s[0]) or is_variable(s[0]):
            term = s[0]
            if len(s) == 1:
                return Term(term), ""
            for idx, char in enumerate(s[1:]):
                if is_alphanumeric(char):
                    term += char
                else:
                    return Term(term), s[idx + 1:]
            # if got here the remainder is empty
            return Term(term), ""
        # else - must be function
        else:
            assert is_function(s[0])
            function_name = s[0]

            idx_start = 0  # idx of '(' in function
            for idx, char in enumerate(s[1:]):
                if char != '(':
                    function_name += char
                else:
                    idx_start = idx
                    break
            _term, _remainder = Term.parse_prefix(s[idx_start + 2:])
            tuple_to_return = list()
            tuple_to_return.append(_term)
            while _remainder[0] != ')':
                _term, _remainder = Term.parse_prefix(_remainder[1:])
                tuple_to_return.append(_term)
            return Term(function_name, tuple_to_return), _remainder[1:]

    @staticmethod
    def parse(s: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            s: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2
        return Term.parse_prefix(s)[0]


    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5.1
        lst_of_constant = list()
        if is_constant(self.root):
            lst_of_constant.append(self.root)
        try:
            for _term in self.arguments:
                lst_of_constant += _term.constants()
        except AttributeError:
            pass
        return set(lst_of_constant)

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5.2
        lst_of_variable = list()
        if is_variable(self.root):
            lst_of_variable.append(self.root)
        try:
            for _term in self.arguments:
                lst_of_variable += _term.variables()
        except AttributeError:
            pass
        return set(lst_of_variable)


    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5.3
        lst_of_functions = list()
        if is_function(self.root):
            lst_of_functions.append((self.root, len(self.arguments), ))
        try:
            for _term in self.arguments:
                lst_of_functions += _term.functions()
        except AttributeError:
            pass
        return set(lst_of_functions)

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1
        new_arg_lst = list()
        if is_function(self.root):
            for idx,arg in enumerate(self.arguments):
                if is_function(arg.root):
                    new_arg_lst.append(arg.substitute(substitution_map,
                                                      forbidden_variables))
                else:
                    # if need to substitute this variable or constant
                    if arg.root in substitution_map:
                        substitute_term = substitution_map[arg.root]
                        # if the substituted term contain forbidden var,
                        # the the below function will raise exception
                        check_if_term_contain_illegal_var(substitute_term
                                                          ,forbidden_variables)
                        # else, its legal term
                        new_arg_lst.append(substitute_term)
                    # if no need to substitute this variable or constant
                    else:
                        new_arg_lst.append(self.arguments[idx])
        else:
            if self.root in substitution_map:
                substitute_term = substitution_map[self.root]
                # if the substituted term contain forbidden var,
                # the the below function will raise exception
                check_if_term_contain_illegal_var(substitute_term,
                                                  forbidden_variables)
                # if got here, the substitute_term term not contain forbidden var
                return substitute_term
        if len(new_arg_lst) == 0:
            return Term(self.root)
        else:
            return Term(self.root, new_arg_lst)

def is_equality(s: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return s == '='

def is_relation(s: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s == '&' or s == '|' or s == '->'

def is_quantifier(s: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return s == 'A' or s == 'E'

"""
Used this function for task 9.2,
This function getting a dict, and unwanted element, 
and return the copy of the dict without this element, or the dict it self 
if it already does not contain that element
"""
def copy_dict_without_one_element(_dict, element_to_remove):
    # if the element already not in the dict, than return the dict as is.
    if not element_to_remove in _dict:
        return _dict
    new_dict = dict(_dict) # shallow copy
    del new_dict[element_to_remove]
    return new_dict

@frozen
class Formula:
    """An immutable first-order formula in tree representation, composed from
    relation names applied to first-order terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the the root, if
                the root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate           
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        final_str = ""
        if is_unary(self.root):
            return "~" + str(self.first)
        elif is_binary(self.root):
            return "(" + str(self.first) + self.root + str(self.second) + ")"
        elif is_equality(self.root):
            return str(self.arguments[0]) + "=" + str(self.arguments[1])
        elif is_function(self.root) or is_relation(self.root):
            final_str += self.root + "("
            for idx, arg in enumerate(self.arguments):
                final_str += str(arg)
                if idx != len(self.arguments) - 1:
                    final_str += ","
            final_str += ")"
            return final_str
        # if root is A or E
        elif is_quantifier(self.root):
            return self.root + self.variable + "[" + str(self.predicate) + "]"

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1
        # An equality of the form ‘t1=t2’, where t1 and t2 are valid terms.
        if is_constant(s[0]) or is_function(s[0]) or is_variable(s[0]):
            term1, _suffix1 = Term.parse_prefix(s)
            term2, _suffix2 = Term.parse_prefix(_suffix1[1:])
            return Formula('=', [term1, term2]), _suffix2

        if is_relation(s[0]):
            lst_arg = list()
            # parsing the name of the relation
            relation_name = s[0]
            s = s[1:]
            lst_idx = 1
            for idx, char in enumerate(s):
                if is_alphanumeric(char):
                    relation_name += char
                else:
                    lst_idx = idx
                    break
            s = s[lst_idx:]
            assert s[0] == '('  # we can assume prefix that is a valid
            s = s[1:]
            # parsing the arguments of the relation
            # case of R()
            if s[0] == ")":
                return Formula(relation_name, []), s[1:]
            _term, _remainder = Term.parse_prefix(s)
            while _remainder[0] == ",":
                lst_arg.append(_term)
                _term, _remainder = Term.parse_prefix(_remainder[1:])
            lst_arg.append(_term)
            if len(_remainder) > 1:
                return Formula(relation_name, lst_arg), _remainder[1:]
            else:
                return Formula(relation_name, lst_arg), ""

        if is_unary(s[0]):
            _prefix, _suffix = Formula.parse_prefix(s[1:])
            return Formula('~', _prefix), _suffix

        # case where is (f1*f2) where * is binary operation
        if s[0] == '(':
            f1, _suffix1 = Formula.parse_prefix(s[1:])
            # when the binary operator is : '&' or '|'
            if is_binary(_suffix1[0]):
                operator = _suffix1[0]
                f2, _suffix2 = Formula.parse_prefix(_suffix1[1:])
                return Formula(operator, f1, f2), _suffix2[1:]
            else:  # case of '->'
                f2, _suffix2 = Formula.parse_prefix(_suffix1[2:])
                return Formula('->', f1, f2), _suffix2[1:]

        # quantification
        else:
            assert s[0] == 'A' or s[0] == 'E'
            quantifier = s[0]
            s = s[1:]
            var_name = ""
            for idx, char in enumerate(s):
                if char == '[':
                    var_name = s[:idx]
                    s = s[idx:]
                    break
            formula, _suffix = Formula.parse_prefix(s[1:])
            return Formula(quantifier, var_name, formula), _suffix[1:]

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        return Formula.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6.1
        set_of_constants = set()
        if is_unary(self.root):
            for const in self.first.constants():
                set_of_constants.add(const)

        elif is_binary(self.root):
            for const in self.first.constants():
                set_of_constants.add(const)
            for const in self.second.constants():
                set_of_constants.add(const)

        elif is_relation(self.root) or is_equality(self.root):
            for _term in self.arguments:
                for const in _term.constants():
                    set_of_constants.add(const)

        elif is_function(self.root):
            for _term in self.arguments:
                set_of_constants.add(_term.constants())

        elif is_quantifier(self.root):
            for const in self.predicate.constants():
                set_of_constants.add(const)
        else:
            if is_constant(self.root):
                set_of_constants.add(self.root)
        return set_of_constants

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6.2
        set_of_variables = set()
        if is_unary(self.root):
            for var in self.first.variables():
                set_of_variables.add(var)

        elif is_binary(self.root):
            for var in self.first.variables():
                set_of_variables.add(var)
            for var in self.second.variables():
                set_of_variables.add(var)

        elif is_relation(self.root) or is_equality(self.root):
            for _term in self.arguments:
                for var in _term.variables():
                    set_of_variables.add(var)

        elif is_function(self.root):
            for _term in self.arguments:
                set_of_variables.add(_term.variables())

        elif is_quantifier(self.root):
            for var in self.predicate.variables():
                set_of_variables.add(var)
            set_of_variables.add(self.variable)
        else:
            if is_variable(self.root):
                set_of_variables.add(self.root)

        return set_of_variables

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of all variable names used in the current formula not only
            within a scope of a quantification on those variable names.
        """
        # Task 7.6.3
        lst_of_variables = set()
        if is_quantifier(self.root):
            for var in self.predicate.free_variables():
                lst_of_variables.add(var)
            # remove e.g Ax(Q(x,w)) - removing x as its not free var
            if self.variable in lst_of_variables:
                lst_of_variables.remove(self.variable)
        elif is_function(self.root):
            for var in self.arguments:
                lst_of_variables.add(var.variables())
        elif is_binary(self.root):
            for var in self.first.free_variables():
                lst_of_variables.add(var)
            for var in self.second.free_variables():
                lst_of_variables.add(var)
        elif is_relation(self.root) or is_equality(self.root):
            for _term in self.arguments:
                for var in _term.variables():
                    lst_of_variables.add(var)
        elif is_unary(self.root):
            for var in self.first.free_variables():
                lst_of_variables.add(var)
        else:
            if is_variable(self.root):
                lst_of_variables.add(self.root)

        return lst_of_variables

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6.4
        set_of_functions = set()
        if is_unary(self.root):
            for func_tuple in self.first.functions():
                set_of_functions.add(func_tuple)

        elif is_binary(self.root):
            for func_tuple in self.first.functions():
                set_of_functions.add(func_tuple)
            for func_tuple in self.second.functions():
                set_of_functions.add(func_tuple)

        elif is_relation(self.root) or is_equality(self.root):
            for _term in self.arguments:
                for func_tuple in _term.functions():
                    set_of_functions.add(func_tuple)

        elif is_function(self.root):
            set_of_functions.add((self.root, len(self.arguments)))

        elif is_quantifier(self.root):
            for var in self.predicate.functions():
                set_of_functions.add(var)
        else:
            if is_function(self.root):
                set_of_functions.add((self.root, len(self.arguments)))

        return set_of_functions

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        set_of_relations = set()

        if is_relation(self.root):
            set_of_relations.add((self.root, len(self.arguments)))

        elif is_unary(self.root):
            for relations_tuple in self.first.relations():
                set_of_relations.add(relations_tuple)

        elif is_binary(self.root):
            for relations_tuple in self.first.relations():
                set_of_relations.add(relations_tuple)
            for relations_tuple in self.second.relations():
                set_of_relations.add(relations_tuple)

        elif is_quantifier(self.root):
            for _relations in self.predicate.relations():
                set_of_relations.add(_relations)
        else:
            if is_function(self.root):
                set_of_relations.add((self.root, len(self.arguments)))

        return set_of_relations


    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2
        if is_relation(self.root) or is_equality(self.root):
            new_arg = list()
            for arg in self.arguments:
                new_arg.append(arg.substitute(substitution_map,
                                              forbidden_variables))
            return Formula(self.root, new_arg)

        elif is_binary(self.root):
            # recursively call first and second (first , binary_operator, second)
            return Formula(self.root,
                           self.first.substitute(substitution_map,
                                                 forbidden_variables),
                           self.second.substitute(substitution_map,
                                                 forbidden_variables))
        else:
            # must be quantifier (for example Ax(x=plus(x,0)))
            assert is_quantifier(self.root)
            # creating new_forbidden_var in order to raise an error when :
            #  'variable occurrence that becomes bound when that term is
            #    substituted into the current formula'
            # just adding self.variable to forbidden variable
            new_forbidden_var = list()
            for _forbidden_var in forbidden_variables:
                new_forbidden_var.append(_forbidden_var)
            new_forbidden_var.append(self.variable)

            new_predicate = self.predicate.substitute(
                copy_dict_without_one_element(substitution_map, self.variable),
                                              new_forbidden_var)
            return Formula(self.root, self.variable, new_predicate)

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a map from each atomic
            propositional formula to the subformula for which it was
            substituted.
        """
        # Task 9.6

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a first-order formula from a propositional skeleton and a
        substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute.
            substitution_map: a map from each atomic propositional subformula
                of the given skeleton to a first-order formula.

        Returns:
            A first-order formula obtained from the given propositional skeleton
            by substituting each atomic propositional subformula with the formula
            mapped to it by the given map.
        """
        for key in substitution_map:
            assert is_propositional_variable(key)
        # Task 9.10
