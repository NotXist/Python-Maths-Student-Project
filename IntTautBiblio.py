from dataclasses import dataclass, field
from enum import Enum, auto
from collections import OrderedDict
from copy import deepcopy

class FormulaSyntaxError(Exception):
    ...

class operation(Enum):
    conjunction=auto()
    disjunction=auto()
    implication=auto()

@dataclass(frozen=True, eq=True)
class Bot():
    def __str__(self) -> str:
        return "0"
    __repr__=__str__

@dataclass(frozen=True, eq=True)
class Prop():
    name: str = field(default="empty")
    def __str__(self) -> str:
        return self.name
    __repr__=__str__


class BinaryTree():
    def __init__(self, value, left_child: "BinaryTree" = None, right_child: "BinaryTree" = None):
        self.value=value
        self.left=left_child
        self.right=right_child

class Formula(BinaryTree):
    def __init__(self, operator, left_subf: "Formula" = None, right_subf: "Formula" = None):
        if (left_subf != None and type(left_subf) != type(self)) or (right_subf != None and type(right_subf) != type(self)):
            raise FormulaSyntaxError("Cannot construct a formula from objects that are not formulas")
        if left_subf==None and right_subf==None:
            if type(operator) != Prop and type(operator) != Bot:
                raise FormulaSyntaxError("An atomic formula can be created only from propositional variables and constant bot")
            super().__init__(operator)
        elif left_subf != None and right_subf != None:
            if type(operator) != type(operation.conjunction):
                raise FormulaSyntaxError("Invalid operation for creating a non-atomic formula")
            super().__init__(operator, left_subf, right_subf)
        else:
            raise FormulaSyntaxError("One argument for binary operation is missing")

    def conj(self, other: "Formula") -> "Formula":
        return self.__class__(operation.conjunction, self, other)
    def disj(self, other: "Formula") -> "Formula":
        return self.__class__(operation.disjunction, self, other)
    def impl(self, other: "Formula") -> "Formula":
        return self.__class__(operation.implication, self, other)
    def neg(self) -> "Formula":
        return self.__class__(operation.implication, self, self.__class__(Bot()))

    def __and__(self, other: "Formula") -> "Formula":
        return self.__class__(operation.conjunction, self, other)
    def __or__(self, other: "Formula") -> "Formula":
        return self.__class__(operation.disjunction, self, other)
    def __rshift__(self, other: "Formula") -> "Formula":
        return self.__class__(operation.implication, self, other)
    def __invert__(self) -> "Formula":
        return self.__class__(operation.implication, self, self.__class__(Bot()))

    @classmethod
    def conjunction(cls, left_subf: "Formula", right_subf: "Formula") -> "Formula":
        return cls(operation.conjunction, left_subf, right_subf)
    @classmethod
    def disjunction(cls, left_subf: "Formula", right_subf: "Formula") -> "Formula":
        return cls(operation.disjunction, left_subf, right_subf)
    @classmethod
    def implication(cls, left_subf: "Formula", right_subf: "Formula") -> "Formula":
        return cls(operation.implication, left_subf, right_subf)
    @classmethod
    def negation(cls, left_subf: "Formula") -> "Formula":
        return cls(operation.implication, left_subf, cls(Bot()))

    @classmethod
    def build(cls, formula: str) -> "Formula":
        if len(formula)==0:
            raise FormulaSyntaxError("Empty formula is invalid")
        Alphabet={
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
        "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z",
        }
        def find_end_of_subform(form: str, start: int) -> int:
            counter = 0
            for j in range(start, len(form)):
                if form[j]=="(":
                    counter+=1
                elif form[j]==")":
                    counter-=1
                    if counter==0:
                        return j
            raise FormulaSyntaxError("Bracket misalignment")
        def find_end_of_prop(form: str, start: int) -> int:
            for j in range(start,len(form)):
                if form[j] not in Alphabet:
                    return j
            return len(form)
        end_of_subf=0
        command_list=[]
        last_seen_element=None
        negations_counter=0
        add_element=None
        i=0
        while i < len(formula):
            if formula[i]=="~":
                if last_seen_element==Prop:
                    raise FormulaSyntaxError("Negation is not a binary operation")
                negations_counter+=1
                i+=1
                last_seen_element=Bot
            elif formula[i]=="(":
                if last_seen_element==Prop:
                    raise FormulaSyntaxError("Operation between two parts of the formula is missing in string")
                end_of_subf=find_end_of_subform(formula, i)
                add_element=cls.build(formula[i+1:end_of_subf])
                for n in range(0, negations_counter):
                    add_element=cls.negation(add_element)
                negations_counter=0
                command_list.append(add_element)
                i=end_of_subf+1
                last_seen_element=Prop
            elif formula[i]=="&" or formula[i]=="|" or formula[i]==">":
                if last_seen_element != Prop:
                    raise FormulaSyntaxError("Formula before operation is missing in string")
                if formula[i]==">":
                    if i+1==len(formula) or formula[i+1]!=">":
                        raise FormulaSyntaxError("String contains non-complete implication")
                    command_list.append(">>")
                    i+=2
                else:
                    command_list.append(formula[i])
                    i+=1
                last_seen_element=operation
            else:
                if formula[i]!="0" and formula[i] not in Alphabet:
                    raise FormulaSyntaxError("Invalid symbols in string (probably incorrect name for propositional variable)")
                if last_seen_element==Prop:
                    raise FormulaSyntaxError("Operation between two parts of the formula is missing in string")
                if formula[i]=="0":
                    add_element=cls(Bot())
                    for n in range(0, negations_counter):
                        add_element=cls.negation(add_element)
                    negations_counter=0
                    command_list.append(add_element)
                    i+=1
                    last_seen_element=Prop
                else:
                    end_of_subf=find_end_of_prop(formula, i)
                    add_element=cls(Prop(formula[i:end_of_subf]))
                    for n in range(0, negations_counter):
                        add_element=cls.negation(add_element)
                    negations_counter=0
                    command_list.append(add_element)
                    i=end_of_subf
                    last_seen_element=Prop
        if last_seen_element != Prop:
            raise FormulaSyntaxError("String ends with operation")
        i=0
        while i<len(command_list):
            if command_list[i]==">>":
                add_element=cls.implication(command_list[i-1],command_list[i+1])
                command_list[i-1]=add_element
                del command_list[i:i+2]
            else:
                i+=1
        i=0
        while i<len(command_list):
            if command_list[i]=="&":
                add_element=cls.conjunction(command_list[i-1],command_list[i+1])
                command_list[i-1]=add_element
                del command_list[i:i+2]
            else:
                i+=1
        i=0
        while i<len(command_list):
            if command_list[i]=="|":
                add_element=cls.disjunction(command_list[i-1],command_list[i+1])
                command_list[i-1]=add_element
                del command_list[i:i+2]
            else:
                i+=1
        add_element=command_list[0]
        return add_element

    @classmethod
    def equality(cls, form_1: "Formula", form_2: "Formula") -> bool:
        if form_1==None and form_2==None:
            return True
        if (form_1!=None and form_2==None) or (form_1==None and form_2!=None):
            return False
        if type(form_1) != cls or type(form_2) != cls:
            raise TypeError("'Formula.equality' not supported between instances of non-formula")
        return form_1.value==form_2.value and cls.equality(form_1.left, form_2.left) and cls.equality(form_1.right, form_2.right)

    def is_atomic(self) -> bool:
        if type(self.value) == type(operation.conjunction):
            return False
        return True

    def __str__(self) -> str:
        if type(self.value) != type(operation.conjunction):
            return str(self.value)
        elif self.value == operation.conjunction:
            return f"({str(self.left)}&{str(self.right)})"
        elif self.value == operation.disjunction:
            return f"({str(self.left)}|{str(self.right)})"
        elif self.value == operation.implication:
            if self.right.value==Bot():
                return f"~{str(self.left)}"
            return f"({str(self.left)}>>{str(self.right)})"
    def __repr__(self) -> str:
        if type(self.value) != type(operation.conjunction):
            return repr(self.value)
        elif self.value == operation.conjunction:
            return f"({repr(self.left)}&{repr(self.right)})"
        elif self.value == operation.disjunction:
            return f"({repr(self.left)}|{repr(self.right)})"
        elif self.value == operation.implication:
            return f"({repr(self.left)}>>{repr(self.right)})"
    @classmethod
    def str_view(cls, formula: "Formula") -> str:
        if type(formula) != cls:
            raise TypeError("Argument must be a formula")
        result=str(formula)
        if (not formula.is_atomic()) and (not result.startswith("~")):
            result=result[1:-1]
        return result

class RuleApplicationError(Exception):
    ...

class Sequence():
    def __init__(self, succedent: Formula, *antecedent: Formula):
        if type(succedent) != Formula:
            raise TypeError("Succedent must be a formula")
        self.succedent = succedent
        self.antecedent=OrderedDict()
        form_str=""
        for item in antecedent:
            if type(item) != Formula:
                raise TypeError("Each element of antecedent must be a formula")
            form_str=str(item)
            self.antecedent.setdefault(form_str,[0,item])
            self.antecedent[form_str][0]+=1

    def is_axiom(self) -> bool:
        check_prop=self.antecedent.get(str(self.succedent),[0])[0]
        check_bot=self.antecedent.get("0",[0])[0]
        if check_bot==0 and check_prop==0:
            return False
        return True
    def is_terminal(self) -> bool:
        if not self.succedent.is_atomic():
            return False
        for item in self.antecedent.keys():
            if (self.antecedent[item][0] != 0) and (not self.antecedent[item][1].is_atomic()):
                if self.antecedent[item][1].value == operation.implication and self.antecedent[item][1].left.is_atomic() and self.antecedent.get(str(self.antecedent[item][1].left), [0])[0] == 0:
                    continue
                return False
        return True

    @classmethod
    def left_conjunction_rule(cls, seq: "Sequence", code: str) -> "Sequence":
        pair=seq.antecedent.get(code)
        if pair == None or pair[0] == 0:
            raise RuleApplicationError("No such formula in the antecedent of the sequence")
        if pair[1].value != operation.conjunction:
            raise RuleApplicationError("Cannot apply conjunction rule to a non-conjunction formula")
        result=cls(seq.succedent)
        result.antecedent=deepcopy(seq.antecedent)
        result.antecedent[code][0]-=1
        code_1=str(pair[1].left)
        result.antecedent.setdefault(code_1, [0,pair[1].left])
        result.antecedent[code_1][0]+=1
        code_2=str(pair[1].right)
        result.antecedent.setdefault(code_2, [0,pair[1].right])
        result.antecedent[code_2][0]+=1
        return result
    @classmethod
    def right_conjunction_rule(cls, seq: "Sequence") -> ("Sequence", "Sequence"):
        if seq.succedent.value != operation.conjunction:
            raise RuleApplicationError("Cannot apply conjunction rule to a non-conjunction formula")
        result_1=cls(seq.succedent.left)
        result_1.antecedent=deepcopy(seq.antecedent)
        result_2=cls(seq.succedent.right)
        result_2.antecedent=deepcopy(seq.antecedent)
        return (result_1, result_2)
    @classmethod
    def left_disjunction_rule(cls, seq: "Sequence", code: str) -> ("Sequence", "Sequence"):
        pair=seq.antecedent.get(code)
        if pair == None or pair[0] == 0:
            raise RuleApplicationError("No such formula in the antecedent of the sequence")
        if pair[1].value != operation.disjunction:
            raise RuleApplicationError("Cannot apply disjunction rule to a non-disjunction formula")
        result_1=cls(seq.succedent)
        result_1.antecedent=deepcopy(seq.antecedent)
        result_1.antecedent[code][0]-=1
        code_1=str(pair[1].left)
        result_1.antecedent.setdefault(code_1, [0,pair[1].left])
        result_1.antecedent[code_1][0]+=1
        result_2=cls(seq.succedent)
        result_2.antecedent=deepcopy(seq.antecedent)
        result_2.antecedent[code][0]-=1
        code_2=str(pair[1].right)
        result_2.antecedent.setdefault(code_2, [0,pair[1].right])
        result_2.antecedent[code_2][0]+=1
        return (result_1, result_2)
    @classmethod
    def right_disjunction1_rule(cls, seq: "Sequence") -> "Sequence":
        if seq.succedent.value != operation.disjunction:
            raise RuleApplicationError("Cannot apply disjunction rule to a non-disjunction formula")
        result=cls(seq.succedent.left)
        result.antecedent=deepcopy(seq.antecedent)
        return result
    @classmethod
    def right_disjunction2_rule(cls, seq: "Sequence") -> "Sequence":
        if seq.succedent.value != operation.disjunction:
            raise RuleApplicationError("Cannot apply disjunction rule to a non-disjunction formula")
        result=cls(seq.succedent.right)
        result.antecedent=deepcopy(seq.antecedent)
        return result
    @classmethod
    def left_implication02_rule(cls, seq: "Sequence", code: str) -> "Sequence":
        pair=seq.antecedent.get(code)
        if pair == None or pair[0] == 0:
            raise RuleApplicationError("No such formula in the antecedent of the sequence")
        if pair[1].value != operation.implication:
            raise RuleApplicationError("Cannot apply implication rule to a non-implication formula")
        if pair[1].left.value == operation.implication:
            raise RuleApplicationError("'left_implication02_rule' must be applied to a formula with not an implication formula as the left subformula")
        result=cls(seq.succedent)
        result.antecedent=deepcopy(seq.antecedent)
        result.antecedent[code][0]-=1
        if pair[1].left.value == operation.conjunction:
            form_1=pair[1].left.left>>(pair[1].left.right>>pair[1].right)
            code_1=str(form_1)
            result.antecedent.setdefault(code_1, [0,form_1])
            result.antecedent[code_1][0]+=1
        elif pair[1].left.value == operation.disjunction:
            form_1=pair[1].left.left>>pair[1].right
            code_1=str(form_1)
            result.antecedent.setdefault(code_1, [0,form_1])
            result.antecedent[code_1][0]+=1
            form_2=pair[1].left.right>>pair[1].right
            code_2=str(form_2)
            result.antecedent.setdefault(code_2, [0,form_2])
            result.antecedent[code_2][0]+=1
        else:
            if seq.antecedent.get(str(pair[1].left), [0])[0] == 0:
                raise RuleApplicationError("There must be an atomic formula in antecedent to apply left implication rule to implication from the atomic formula")
            form_1=pair[1].right
            code_1=str(form_1)
            result.antecedent.setdefault(code_1, [0,form_1])
            result.antecedent[code_1][0]+=1
        return result
    @classmethod
    def left_implication3_rule(cls, seq: "Sequence", code: str) -> ("Sequence", "Sequence"):
        pair=seq.antecedent.get(code)
        if pair == None or pair[0] == 0:
            raise RuleApplicationError("No such formula in the antecedent of the sequence")
        if pair[1].value != operation.implication:
            raise RuleApplicationError("Cannot apply implication rule to a non-implication formula")
        if pair[1].left.value != operation.implication:
            raise RuleApplicationError("'left_implication3_rule' must be applied to a formula with an implication formula as the left subformula")
        result_1=cls(seq.succedent)
        result_1.antecedent=deepcopy(seq.antecedent)
        result_1.antecedent[code][0]-=1
        form_1=pair[1].right
        code_1=str(form_1)
        result_1.antecedent.setdefault(code_1, [0,form_1])
        result_1.antecedent[code_1][0]+=1
        result_0=cls(pair[1].left.right)
        result_0.antecedent=deepcopy(seq.antecedent)
        result_0.antecedent[code][0]-=1
        code_0=str(pair[1].left.left)
        result_0.antecedent.setdefault(code_0, [0,pair[1].left.left])
        result_0.antecedent[code_0][0]+=1
        form_0=pair[1].left.right>>pair[1].right
        code_0=str(form_0)
        result_0.antecedent.setdefault(code_0, [0,form_0])
        result_0.antecedent[code_0][0]+=1
        return (result_0, result_1)
    @classmethod
    def right_implication_rule(cls, seq: "Sequence") -> "Sequence":
        if seq.succedent.value != operation.implication:
            raise RuleApplicationError("Cannot apply implication rule to a non-implication formula")
        result=cls(seq.succedent.right)
        result.antecedent=deepcopy(seq.antecedent)
        code=str(seq.succedent.left)
        result.antecedent.setdefault(code, [0,seq.succedent.left])
        result.antecedent[code][0]+=1
        return result

    def __str__(self) -> str:
        result=""
        for item in self.antecedent.keys():
            for i in range(0, self.antecedent[item][0]):
                if item.startswith("("):
                    result+=item[1:-1] + ", "
                else:
                    result+=item + ", "
        result=result[:-2] + " => " + Formula.str_view(self.succedent)
        return result
    def __repr__(self) -> str:
        result=""
        for item in self.antecedent.keys():
            for i in range(0, self.antecedent[item][0]):
                result+=item + ", "
        result=result[:-2] + " => " + str(self.succedent)
        return result

class rule(Enum):
    left_conjunction=auto()
    left_disjunction=auto()
    left_implication02=auto()
    left_implication3=auto()
    right_conjunction=auto()
    right_disjunction1=auto()
    right_disjunction2=auto()
    right_implication=auto()
    axiom=auto()
    terminal=auto()

class Derivation(BinaryTree):
    def __init__(self, applying_rule, code: str, seq: Sequence, left_der: "Derivation" = None, right_der: "Derivation" = None, previous_der: "Derivation" = None):
        super().__init__(seq, left_der, right_der)
        if type(applying_rule) != type(rule.axiom):
            raise RuleApplicationError("First argument of 'Derivation' must be a rule")
        self.applying=applying_rule
        self.formula=code
        self.next=previous_der

def DerivationSearch(seq: Sequence) -> Derivation:
    if type(seq) != Sequence:
        raise TypeError("Argument must be a sequence")
    if seq.is_axiom():
        if seq.antecedent.get("0",[0])[0] != 0:
            return Derivation(rule.axiom, "0", seq)
        return Derivation(rule.axiom, str(seq.succedent), seq)
    if seq.is_terminal():
        return None
    if not seq.succedent.is_atomic() and seq.succedent.value != operation.disjunction:
        if seq.succedent.value==operation.implication:
            der_0=DerivationSearch(Sequence.right_implication_rule(seq))
            if der_0==None:
                return None
            result=Derivation(rule.right_implication, str(seq.succedent), seq, der_0)
            der_0.next=result
            return result
        elif seq.succedent.value==operation.conjunction:
            seq_0, seq_1 = Sequence.right_conjunction_rule(seq)
            der_0=DerivationSearch(seq_0)
            if der_0==None:
                return None
            der_1=DerivationSearch(seq_1)
            if der_1==None:
                return None
            result=Derivation(rule.right_conjunction, str(seq.succedent), seq, der_0, der_1)
            der_0.next=result
            der_1.next=result
            return result
    else:
        for item in seq.antecedent.keys():
            if seq.antecedent[item][0]!=0:
                formula=seq.antecedent[item][1]
                code=str(formula)
                if formula.is_atomic():
                    continue
                if formula.value==operation.conjunction:
                    seq_0=Sequence.left_conjunction_rule(seq, code)
                    seq_0.antecedent.move_to_end(code)
                    der_0=DerivationSearch(seq_0)
                    if der_0==None:
                        return None
                    result=Derivation(rule.left_conjunction, code, seq, der_0)
                    der_0.next=result
                    return result
                elif formula.value==operation.disjunction:
                    seq_0, seq_1 = Sequence.left_disjunction_rule(seq, code)
                    seq_0.antecedent.move_to_end(code)
                    seq_1.antecedent.move_to_end(code)
                    der_0=DerivationSearch(seq_0)
                    if der_0==None:
                        return None
                    der_1=DerivationSearch(seq_1)
                    if der_1==None:
                        return None
                    result=Derivation(rule.left_disjunction, code, seq, der_0, der_1)
                    der_0.next=result
                    der_1.next=result
                    return result
                elif formula.value==operation.implication:
                    if formula.left.is_atomic():
                        if seq.antecedent.get(str(formula.left), [0])[0] == 0:
                            continue
                        seq_0=Sequence.left_implication02_rule(seq, code)
                        seq_0.antecedent.move_to_end(code)
                        der_0=DerivationSearch(seq_0)
                        if der_0==None:
                            return None
                        result=Derivation(rule.left_implication02, code, seq, der_0)
                        der_0.next=result
                        return result
                    elif formula.left.value==operation.conjunction or formula.left.value==operation.disjunction:
                        seq_0=Sequence.left_implication02_rule(seq, code)
                        seq_0.antecedent.move_to_end(code)
                        der_0=DerivationSearch(seq_0)
                        if der_0==None:
                            return None
                        result=Derivation(rule.left_implication02, code, seq, der_0)
                        der_0.next=result
                        return result
                    elif formula.left.value==operation.implication:
                        seq_0, seq_1 = Sequence.left_implication3_rule(seq, code)
                        seq_0.antecedent.move_to_end(code)
                        seq_1.antecedent.move_to_end(code)
                        der_1=DerivationSearch(seq_1)
                        if der_1==None:
                            return None
                        der_0=DerivationSearch(seq_0)
                        if der_0==None:
                            continue
                        result=Derivation(rule.left_implication3, code, seq, der_0, der_1)
                        der_0.next=result
                        der_1.next=result
                        return result
        if seq.succedent.value == operation.disjunction:
            seq_0=Sequence.right_disjunction1_rule(seq)
            der_0=DerivationSearch(seq_0)
            if der_0 != None:
                result=Derivation(rule.right_disjunction1, str(seq.succedent), seq, der_0)
                der_0.next=result
                return result
            seq_1=Sequence.right_disjunction2_rule(seq)
            der_1=DerivationSearch(seq_1)
            if der_1 != None:
                result=Derivation(rule.right_disjunction2, str(seq.succedent), seq, der_1)
                der_1.next=result
                return result
    return None

