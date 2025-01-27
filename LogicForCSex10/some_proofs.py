# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/some_proofs.py

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
# from predicates.deduction import *
# from predicates.prenex import equivalence_of

def syllogism_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.qed()

def syllogism_proof_with_universal_instantiation(print_as_proof_forms: bool =
                                                 False) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.qed()

def syllogism_all_all_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.qed()

def syllogism_all_all_proof_with_tautological_implication(print_as_proof_forms:
                                                          bool = False) -> \
        Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_implication(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.qed()

def syllogism_all_exists_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R': 'Man(_)', 'Q': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_implication(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.qed()

def syllogism_all_exists_proof_with_existential_derivation(print_as_proof_forms:
                                                           bool = False) -> \
        Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.qed()

def lovers_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)
    
    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'},
                    print_as_proof_forms)
    # Task 10.4
    assumption1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    assumption2 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')

    # (Ax[Ey[Loves(x,y)]]->Ey[Loves(x,y)]) UI on assumption1
    step3 = prover.add_instantiated_assumption\
        ('(Ax[Ey[Loves(x,y)]]->Ey[Loves(x,y)])',
         Prover.UI,
         {'x':'x', 'R':'Ey[Loves(_,y)]', 'c':'x'})

    # using MP on step3 and assumption 1 in order to get Ey[Loves(x,y)]
    step4 = prover.add_mp('Ey[Loves(x,y)]', assumption1, step3)
    # step3 and 4 can be combined with one line, using add_universal_instantiation
    # prover.add_universal_instantiation('Ey[Loves(x,y)]', assumption1, 'x')

    step5 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', assumption2, 'x')

    step6 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step5, 'z')

    step7 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step6, 'y')

    step8 = prover.add_existential_derivation('Loves(z,x)', step4, step7)

    step9 = prover.add_ug('Az[Loves(z,x)]', step8)

    step10 = prover.add_ug('Ax[Az[Loves(z,x)]]', step9)

    return prover.qed()

def homework_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)
    
    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'}, print_as_proof_forms)
    # Task 10.5
    step1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step2 = prover.add_instantiated_assumption(
        '((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI,
        {'R': '(Homework(_)&Fun(_))', 'c': 'x'})
    step3 = prover.add_instantiated_assumption(
        '((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI,
        {'R': '(Reading(_)&~Fun(_))', 'c': 'x'})
    step4 = prover.add_tautological_implication(
        '((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])', {step1,
                                                                 step2, step3})
    step5 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')

    step6 = prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]',
                                              step5, step4)

    return prover.qed()

#: The three group axioms
GROUP_AXIOMS = frozenset({'plus(0,x)=x', 'plus(minus(x),x)=0',
                          'plus(plus(x,y),z)=plus(x,plus(y,z))'})

def right_neutral_proof(stop_before_flipped_equality: bool,
                        stop_before_free_instantiation: bool,
                        stop_before_substituted_equality: bool,
                        stop_before_chained_equality: bool,
                        print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof constructed up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof constructed up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof constructed up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof constructed up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(_,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(_,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),_),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),_)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),_)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)', flipped_associativity,
        {'x': 'minus(minus(x))','y': 'minus(x)','z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(_,x)')
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.qed()

def unique_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), print_as_proof_forms)
    # Task 10.10
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption(
        'plus(plus(x,y),z)=plus(x,plus(y,z))')
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    zero_inst = prover.add_free_instantiation('plus(minus(a),a)=0', negation,
                                              {'x': 'a'})
    flipped_zero_inst = prover.add_flipped_equality('0=plus(minus(a),a)', zero_inst)

    assumption = prover.add_assumption('plus(a,c)=a')
    step1 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)',
                                            assumption,
                                            Term.parse('plus(minus(a),_)'))
    step2 = prover.add_flipped_equality('plus(minus(a),a)=plus(minus(a),plus(a,c))',
                                        step1)
    _map_step3 = {'x': 'minus(a)', 'y': 'a', 'z': 'c'}
    step3 = prover.add_free_instantiation(
        'plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)',
        flipped_associativity, _map_step3)
    step4 = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)',
                                            zero_inst, 'plus(_,c)')
    step5 = prover.add_free_instantiation('plus(0,c)=c', zero, {'x':'c'})
    step6 = prover.add_chained_equality('0=c', [flipped_zero_inst, step2, step3,
                                                step4, step5])
    step7 = prover.add_flipped_equality('c=0', step6)
    return prover.qed()

#: The six field axioms
FIELD_AXIOMS = frozenset(GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'}))

def multiply_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # Task 10.11
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption(
        'plus(plus(x,y),z)=plus(x,plus(y,z))')
    distributivity = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    multiplication_commutativity = prover.add_assumption('times(x,y)=times(y,x)')
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    zero_inst = prover.add_free_instantiation('plus(minus(times(0,x)),times(0,x))=0', negation,
                                              {'x': 'times(0,x)'})
    flipped_zero_inst = prover.add_flipped_equality('0=plus(minus(times(0,x)),times(0,x))', zero_inst)

    step1a = prover.add_free_instantiation('times(0,x)=times(x,0)',
                                           multiplication_commutativity,
                                           {'x': '0', 'y': 'x'})
    step2a = prover.add_free_instantiation('0=plus(0,0)', flipped_zero, {'x': '0'})
    step3a = prover.add_substituted_equality('times(x,0)=times(x,plus(0,0))',
                                             step2a, 'times(x,_)')
    step4a = prover.add_free_instantiation(
        'times(x,plus(0,0))=plus(times(x,0),times(x,0))', distributivity,
        {'y': '0', 'z': '0'})
    step5a = prover.add_free_instantiation(
        'times(x,0)=times(0,x)', multiplication_commutativity, {'x': 'x', 'y': '0'})
    step6a = prover.add_substituted_equality(
        'plus(times(x,0),times(x,0))=plus(times(0,x),times(0,x))', step5a,
        'plus(_,_)')
    step7a = prover.add_chained_equality('times(0,x)=plus(times(0,x),times(0,x))',
                                         [step1a, step3a, step4a, step6a])

    last_a = prover.add_flipped_equality('plus(times(0,x),times(0,x))=times(0,x)',
                                         step7a)
    step1b = prover.add_substituted_equality(
        'plus(minus(times(0,x)),plus(times(0,x),times(0,x)))=plus(minus(times(0,x)),times(0,x))',
        last_a,
        Term.parse('plus(minus(times(0,x)),_)'))
    step2b = prover.add_flipped_equality(
        'plus(minus(times(0,x)),times(0,x))=plus(minus(times(0,x)),plus(times(0,x),times(0,x)))',
        step1b)
    _map_step3b = {'x': 'minus(times(0,x))', 'y': 'times(0,x)', 'z': 'times(0,x)'}
    step3b = prover.add_free_instantiation(
        'plus(minus(times(0,x)),plus(times(0,x),times(0,x)))=plus(plus(minus(times(0,x)),times(0,x)),times(0,x))',
        flipped_associativity, _map_step3b)
    step4b = prover.add_substituted_equality(
        'plus(plus(minus(times(0,x)),times(0,x)),times(0,x))=plus(0,times(0,x))',
        zero_inst, 'plus(_,times(0,x))')
    step5b = prover.add_free_instantiation('plus(0,times(0,x))=times(0,x)',
                                           zero, {'x': 'times(0,x)'})
    step6b = prover.add_chained_equality('0=times(0,x)', [flipped_zero_inst, step2b, step3b,
                                                step4b, step5b])
    step7b = prover.add_flipped_equality('times(0,x)=0', step6b)
    return prover.qed()

#: The induction axiom
INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
#: The six axioms of Peano arithmetic
PEANO_AXIOMS = frozenset({'(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                          'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))',
                          'times(x,0)=0', 'times(x,s(y))=plus(times(x,y),x)',
                          INDUCTION_AXIOM})

def peano_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # Task 10.12
    zero = prover.add_assumption('plus(x,0)=x')
    s_assumption = prover.add_assumption('plus(x,s(y))=s(plus(x,y))')
    step1 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    _map_step2 = {'c': 'plus(0,x)',
                  'd': 'x',
                  'R': Formula.parse('plus(0,s(x))=s(_)')}


    formula_for_step2 = Formula('->', Formula.parse('plus(0,s(x))=s(plus(0,x))'),
                                Formula.parse('plus(0,s(x))=s(x)'))
    formula_for_step2 = Formula('->', Formula.parse('plus(0,x)=x'),
                                formula_for_step2)
    step2 = prover.add_instantiated_assumption(formula_for_step2, Prover.ME,
                                             _map_step2)
    step3 = prover.add_free_instantiation('plus(0,s(x))=s(plus(0,x))',
                                          s_assumption, {'x': '0', 'y': 'x'})
    step4 = prover.add_tautological_implication(
        '(plus(0,x)=x->plus(0,s(x))=s(x))', {step3, step2})
    step5 = prover.add_ug('Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]', step4)
    step6 = prover.add_tautological_implication(
        '(plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])',
        {step1, step5})
    step7 = prover.add_instantiated_assumption(
        '((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])',
        INDUCTION_AXIOM, {'R': 'plus(0,_)=_'})
    step8 = prover.add_tautological_implication('Ax[plus(0,x)=x]', {step6,
                                                                    step7})
    step9 = prover.add_universal_instantiation('plus(0,x)=x', step8, 'x')

    return prover.qed()

#: The axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})

def russell_paradox_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    # Task 10.13
    step1_f = Formula.parse('Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]')
    step1 = prover.add_instantiated_assumption(step1_f, COMPREHENSION_AXIOM,
                                               {'R': '~In(_,_)'})
    step2_f = Formula.parse('(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y))))')
    step2 = prover.add_instantiated_assumption(step2_f, prover.UI,
            {'R': '((In(_,y)->~In(_,_))&(~In(_,_)->In(_,y)))', 'x': 'x',
             'c': 'y'})
    step3 = prover.add_tautology('(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z)))')
    step4 = prover.add_tautological_implication(
        '(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))',
        {step2, step3})
    step5 = prover.add_existential_derivation('(z=z&~z=z)', step1, step4)

    return prover.qed()

def not_exists_not_implies_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.1

def exists_not_implies_not_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.2

def not_all_iff_exists_not_proof(formula: Formula, variable: str,
                                 print_as_proof_forms: bool = False) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.3
