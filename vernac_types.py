# Python classes corresponding to OCaml datatypes
# They are used to generate the CFG of the S-expressions, see gallina.py
from collections import OrderedDict
import re


class Type:
    'Abstract class for Ocaml types'
    cache = {}

    def __new__(cls, *args):
        if len(args) == 0:
            nonterminal = cls.__name__.lower()
        else:
            nonterminal = (cls.__name__ + '___' + '____'.join([p.nonterminal for p in args])).lower()
        if hasattr(cls, 'inline') and cls.inline == True:
            nonterminal = '_' + nonterminal

        if nonterminal in Type.cache:
            t = Type.cache[nonterminal]
            t.initialized = True
            return t
        else:
            t = super().__new__(cls)
            t.initialized = False
            t.nonterminal = nonterminal
            Type.cache[nonterminal] = t
            return t

    def parsing_rules(self):
        'return a list of strings (production rules) and a list of symbols (dependencies)'
        raise NotImplementedError

    def to_ebnf(self, recursive=False, skip_symbols=None):
        if skip_symbols is None:
            skip_symbols = set()
        rules, dependencies = self.parsing_rules()
        ebnf = self.nonterminal + ' : ' + ('\n ' + ' ' * len(self.nonterminal) + '| ').join(rules)
        skip_symbols.add('constr__constr')
        if recursive:
            for t in dependencies:
                if not t.nonterminal in skip_symbols:
                    skip_symbols.add(t.nonterminal)
                    ebnf += '\n\n' + t.to_ebnf(True, skip_symbols)       
        return ebnf

    def is_alias_for(self, cls):
        return isinstance(self, cls)
        

class AliasType(Type):

    def __init__(self):
        self.nonterminal = self.alias.nonterminal

    def is_alias_for(self, cls):
        if isinstance(self, cls):
            return True
        else:
            return self.alias.is_alias_for(cls)

    def parsing_rules(self):
        return self.alias.parsing_rules()


class UnimplementedType(Type):

    def parsing_rules(self):
        raise ValueError(self.__class__.__name__ + " unimplemented")


# built-in types

class Int(Type):
    def parsing_rules(self):
        return ['SIGNED_INT'], []


class String(Type):
    def parsing_rules(self):
        return ['ESCAPED_STRING', 'STRING_INNER*'], []


class Bool(Type):
    def parsing_rules(self):
        return ['"true"', '"false"'], []


class Tuple(Type):
    inline = True

    def __init__(self, *args):
        self.types = args

    def parsing_rules(self):
        return ['"(" %s ")"' % ' '.join([e.nonterminal for e in self.types])], self.types


class List(Type):
    inline = True

    def __init__(self, t):
        assert isinstance(t, Type)
        self.t = t

    def parsing_rules(self):
        return ['"(" %s* ")"' % self.t.nonterminal], [self.t]


class Array(Type):
    inline = True

    def __init__(self, t):
        assert isinstance(t, Type)
        self.t = t

    def parsing_rules(self):
        return ['"(" %s* ")"' % self.t.nonterminal], [self.t]


class NonEmptyList(Type):
    def __init__(self, t):
        assert isinstance(t, Type)
        self.t = t

    def parsing_rules(self):
        return ['"(" %s+ ")"' % self.t.nonterminal], [self.t]


class Record(Type):

    def parsing_rules(self):
        return ['"(" %s ")"' % ' '.join(['"(" /%s/ %s ")"' % (k, v.nonterminal) 
                                            for k, v in self.fields.items()])], \
                [v for v in self.fields.values()]


class Variant(Type):

    def parsing_rules(self):
        rules = []
        dependencies = []
        for name, arg_type in self.constructors.items():
            if arg_type is None:
                rules.append('"%s"    -> constructor_%s' % (name, name.lower()))
                continue
            elif isinstance(arg_type, Tuple):
                args = ' '.join([t.nonterminal for t in arg_type.types])
                dependencies.extend(arg_type.types)
            else:
                args = arg_type.nonterminal
                dependencies.append(arg_type)
            rules.append('"(" "%s" %s ")"    -> constructor_%s' % (name, args, name.lower()))
        return rules, dependencies


class Option(Type):
    inline = True

    def __init__(self, t):
        assert isinstance(t, Type)
        self.t = t

    def parsing_rules(self):
        return ['"(" %s? ")"' % self.t.nonterminal], [self.t]


# Coq types

class Univ__Universe__t(AliasType):
    '''
    type t = Level.t * int
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_univ.ml: type _t = (Level.t * int) list'
        self.alias = List(Tuple(Univ__Level__t(), Int()))


class Sorts__t(Variant):
    '''
    type t =
    | Prop
    | Set
    | Type of Univ.Universe.t
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Prop': None,
            'Set': None,
            'Type': Univ__Universe__t(),
        })
    

class Univ__Level__t(Variant):
    '''
    type t = { 
        hash : int;
        data : RawLevel.t }
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_univ.ml: type _level = ULevel of int'
        self.constructors = OrderedDict({
            'ULevel': Int(),
        })


class Univ__Instance__t(Variant):
    '''
    type t = Level.t array
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_univ.ml: type _instance = Instance of Level.t array'
        self.constructors = OrderedDict({
            'Instance': Array(Univ__Level__t()),
        })


class Names__KerPair__t(Variant):
    '''
    type t =
    | Same of KerName.t (** user = canonical *)
    | Dual of KerName.t * KerName.t (** user then canonical *)
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Same': Names__KerName__t(),
            'Dual': Tuple(Names__KerName__t(), Names__KerName__t()),
        })


class Names__Constant__t(Variant):
    '''
    module Constant = KerPair
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_names.ml: type _constant = Constant of ModPath.t * DirPath.t * Label.t'
        self.constructors = OrderedDict({
            'Constant': Tuple(Names__ModPath__t(), Names__DirPath__t(), Names__Label__t()),
        })


class Names__MutInd__t(Variant):
    '''
    module MutInd = KerPair
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_names.ml: type _mutind = Mutind of ModPath.t * DirPath.t * Label.t'
        self.constructors = OrderedDict({
            'Mutind': Tuple(Names__ModPath__t(), Names__DirPath__t(), Names__Label__t()),
        })


class Names__inductive(AliasType):
    '''
    (** Designation of a (particular) inductive type. *)
    type inductive = MutInd.t      (* the name of the inductive type *)
                    * int           (* the position of this inductive type
                                        within the block of mutually-recursive inductive types.
                                        BEWARE: indexing starts from 0. *)
    '''
    def __init__(self):
        self.alias = Tuple(Names__MutInd__t(), Int())


class Names__constructor(AliasType):
    '''
    (** Designation of a (particular) constructor of a (particular) inductive type. *)
    type constructor = inductive   (* designates the inductive type *)
                        * int         (* the index of the constructor
                                        BEWARE: indexing starts from 1. *)
    '''
    def __init__(self):
        self.alias = Tuple(Names__inductive(), Int())


class Constr__case_style(Variant):
    '''
    type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'LetStyle': None,
            'IfStyle': None,
            'LetPatternStyle': None,
            'MatchStyle': None,
            'RegularStyle': None,
        })


class Constr__case_printing(Record):
    '''    
    type case_printing =
    { ind_tags : bool list; (** tell whether letin or lambda in the arity of the inductive type *)
        cstr_tags : bool list array; (* whether each pattern var of each constructor is a let-in (true) or not (false) *)
        style     : case_style }
    '''
    def __init__(self):
        self.fields = OrderedDict({
            'ind_tags': List(Bool()),
            'cstr_tags': Array(List(Bool())),
            'style': Constr__case_style(),
        })


class Constr__case_info(Record):
    '''
    type case_info =
    { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
        ci_npar       : int;            (* number of parameters of the above inductive type *)
        ci_cstr_ndecls : int array;     (* For each constructor, the corresponding integer determines
                                        the number of values that can be bound in a match-construct.
                                        NOTE: parameters of the inductive type are therefore excluded from the count *)
        ci_cstr_nargs : int array;      (* for each constructor, the corresponding integers determines
                                        the number of values that can be applied to the constructor,
                                        in addition to the parameters of the related inductive type
                                        NOTE: "lets" are therefore excluded from the count
                                        NOTE: parameters of the inductive type are also excluded from the count *)
        ci_pp_info    : case_printing   (* not interpreted by the kernel *)
    }
    '''
    def __init__(self):
        self.fields = OrderedDict({
            'ci_ind': Names__inductive(),
            'ci_npar': Int(),
            'ci_cstr_ndecls': Array(Int()),
            'ci_cstr_nargs': Array(Int()),
            'ci_pp_info': Constr__case_printing(),
        })


class Evar__t(Variant):
    '''
    type t = int
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_evar.ml: type _evar = Ser_Evar of int [@@deriving sexp]'
        self.constructors = OrderedDict({
            'Ser_Evar': Int(),
        })


class Constr__existential_key(AliasType):
    '''
    type existential_key = Evar.t
    '''
    def __init__(self):
        self.alias = Evar__t()


class Constr__pexistential(AliasType):
    '''
    type 'constr pexistential = existential_key * 'constr array
    '''
    def __init__(self, constr):
        self.constr = constr
        self.alias = Tuple(Constr__existential_key(), Array(self.constr))
        

class Constr__prec_declaration(AliasType):
    '''
    type ('constr, 'types) prec_declaration =
        Name.t array * 'types array * 'constr array
    '''
    def __init__(self, constr, types):
        self.constr = constr
        self.types = types
        self.alias = Tuple(Array(Names__Name__t()), Array(self.types), Array(self.constr))


class Constr__pfixpoint(AliasType):
    '''
    type ('constr, 'types) pfixpoint =
        (int array * int) * ('constr, 'types) prec_declaration
    '''
    def __init__(self, constr, types):
        self.constr = constr
        self.types = types
        self.alias = Tuple(Tuple(Array(Int()), Int()), Constr__prec_declaration(self.constr, self.types))


class Constr__pcofixpoint(AliasType):
    '''
    type ('constr, 'types) pcofixpoint =
        int * ('constr, 'types) prec_declaration 
    '''
    def __init__(self, constr, types):
        self.constr = constr
        self.types = types
        self.alias = Tuple(Int(), Constr__prec_declaration(self.constr, self.types))


class Names__Projection__t(Variant):
    '''
    type t =
      { proj_ind : inductive;
        proj_npars : int;
        proj_arg : int;
        proj_name : Label.t; }
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_names.ml: type _projection = Projection of Constant.t * bool'
        self.constructors = OrderedDict({
            'Projection': Tuple(Names__Constant__t(), Bool()),
        })


class Constr__cast_kind(Variant):
    '''
    type cast_kind = VMcast | NATIVEcast | DEFAULTcast | REVERTcast
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'VMcast': None,
            'NATIVEcast': None,
            'DEFAULTcast': None,
            'REVERTcast': None,
        })


class Constr__metavariable(AliasType):
    '''
    type metavariable = int
    '''
    def __init__(self):
        self.alias = Int()


class Constr__kind_of_term(Variant):
    '''
    type ('constr, 'types, 'sort, 'univs) kind_of_term =
    | Rel       of int
    | Var       of Id.t
    | Meta      of metavariable
    | Evar      of 'constr pexistential
    | Sort      of 'sort
    | Cast      of 'constr * cast_kind * 'types
    | Prod      of Name.t * 'types * 'types
    | Lambda    of Name.t * 'types * 'constr
    | LetIn     of Name.t * 'constr * 'types * 'constr
    | App       of 'constr * 'constr array
    | Const     of (Constant.t * 'univs)
    | Ind       of (inductive * 'univs)
    | Construct of (constructor * 'univs)
    | Case      of case_info * 'constr * 'constr * 'constr array
    | Fix       of ('constr, 'types) pfixpoint
    | CoFix     of ('constr, 'types) pcofixpoint
    | Proj      of Projection.t * 'constr
    '''
    def __init__(self, constr, types, sort, univs):
        self.constr = constr
        self.types = types
        self.sort = sort
        self.univs = univs
        self.constructors = OrderedDict({
            'Rel': Int(),
            'Var': Names__Id__t(),
            'Meta': Constr__metavariable(),
            'Evar': Constr__pexistential(self.constr),
            'Sort': self.sort,
            'Cast': Tuple(self.constr, Constr__cast_kind(), self.types),
            'Prod': Tuple(Names__Name__t(), self.types, self.types),
            'Lambda': Tuple(Names__Name__t(), self.types, self.constr),
            'LetIn': Tuple(Names__Name__t(), self.constr, self.types, self.constr),
            'App': Tuple(self.constr, Array(self.constr)),
            'Const': Tuple(Tuple(Names__Constant__t(), self.univs)),
            'Ind': Tuple(Tuple(Names__inductive(), self.univs)),
            'Construct': Tuple(Tuple(Names__constructor(), self.univs)),
            'Case': Tuple(Constr__case_info(), self.constr, self.constr, Array(self.constr)),
            'Fix': Constr__pfixpoint(self.constr, self.types),
            'CoFix': Constr__pcofixpoint(self.constr, self.types),
            'Proj': Tuple(Names__Projection__t(), self.constr),
        })
        

class Constr__constr(AliasType):
    '''
    type t = (t, t, Sorts.t, Instance.t) kind_of_term
    type constr = t
    '''
    def __init__(self):
        if self.initialized:
            return
        self.alias = Constr__kind_of_term(Constr__constr(), Constr__constr(), Sorts__t(), Univ__Instance__t())


class Loc__source(Variant):
    constructors = OrderedDict({
        'InFile': String(),
        'ToplevelInput': None,
    })


class Loc__t(Record):
    '''
    type t = {
        fname : source; (** filename or toplevel input *)
        line_nb : int; (** start line number *)
        bol_pos : int; (** position of the beginning of start line *)
        line_nb_last : int; (** end line number *)
        bol_pos_last : int; (** position of the beginning of end line *)
        bp : int; (** start position *)
        ep : int; (** end position *)
    }
    '''
    def __init__(self):
        self.fields = OrderedDict({
            'bp': Int(),
            'ep': Int(),
        })


class Vernacexpr__vernac_flag(Variant):
    def __init__(self):
        self.constructors = OrderedDict({
            'VernacProgram': None,
            'VernacPolymorphic': Bool(),
            'VernacLocal': Bool(),
        })


class Genarg__rlevel(UnimplementedType):
    '''
    type rlevel = [ `rlevel ]
    '''
    pass


class Genarg__glevel(UnimplementedType):
    '''
    type glevel = [ `glevel ]
    '''
    pass


class Genarg__tlevel(UnimplementedType):
    '''
    type tlevel = [ `tlevel ]
    '''
    pass


class Genarg__ArgT__tag(Type):
    '''
    type ('a, 'b, 'c) tag = ('a * 'b * 'c) DYN.tag
    '''
    tags = ['auto_using',
            'bindings',
            'by_arg_tac',
            'casted_constr',
            'clause_dft_concl',
            'constr',
            'constr_with_bindings',
            'destruction_arg',
            'firstorder_using',
            'fun_ind_using',
            'glob_constr_with_bindings',
            'hintbases',
            'ident',
            'in_clause',
            'int_or_var',
            'intropattern',
            'ltac_info',
            'ltac_selector',
            'ltac_use_default',
            'natural',
            'orient',
            'preident',
            'quant_hyp',
            'rename',
            'rewstrategy',
            'ssrapplyarg',
            'ssrarg',
            'ssrcasearg',
            'ssrclauses',
            'ssrcongrarg',
            'ssrdoarg',
            'ssrexactarg',
            'ssrfwdid',
            'ssrhavefwdwbinders',
            'ssrhintarg',
            'ssrintrosarg',
            'ssrmovearg',
            'ssrposefwd',
            'ssrrpat',
            'ssrrwargs',
            'ssrseqarg',
            'ssrseqdir',
            'ssrsetfwd',
            'ssrsufffwd',
            'ssrtclarg',
            'ssrunlockargs',
            'tactic',
            'uconstr',
            'var',
            'with_names']
            
    def parsing_rules(self):
        'coq-serapi/serlib/ser_genarg.ml'
        return ['"%s"' % tag for tag in Genarg__ArgT__tag.tags], []


class Genarg__genarg_type(Variant):
    '''
    type (_, _, _) genarg_type =
    | ExtraArg : ('a, 'b, 'c) ArgT.tag -> ('a, 'b, 'c) genarg_type
    | ListArg : ('a, 'b, 'c) genarg_type -> ('a list, 'b list, 'c list) genarg_type
    | OptArg : ('a, 'b, 'c) genarg_type -> ('a option, 'b option, 'c option) genarg_type
    | PairArg : ('a1, 'b1, 'c1) genarg_type * ('a2, 'b2, 'c2) genarg_type ->
        ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2) genarg_type
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'ExtraArg': Genarg__ArgT__tag(),
            'ListArg': self,
            'OptArg': self,
            'PairArg': Tuple(self, self)
        })


class Locus__occurrences_gen(Variant):
    '''
    type 'a occurrences_gen =
    | AllOccurrences
    | AllOccurrencesBut of 'a list (** non-empty *)
    | NoOccurrences
    | OnlyOccurrences of 'a list (** non-empty *)
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'AllOccurrences': None,
            'AllOccurrencesBut': List(a),
            'NoOccurrences': None,
            'OnlyOccurrences': List(a),
        })



class Locus__occurrences_expr(AliasType):
    '''
    type occurrences_expr = (int or_var) occurrences_gen
    '''
    def __init__(self):
        self.alias = Locus__occurrences_gen(Misctypes__or_var(Int()))


class Locus__with_occurrences(AliasType):
    '''
    type 'a with_occurrences = occurrences_expr * 'a
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.alias = Tuple(Locus__occurrences_expr(), a)


class Util__union(Variant):
    '''
    type ('a, 'b) union = ('a, 'b) CSig.union = Inl of 'a | Inr of 'b
    '''
    def __init__(self, a, b):
        assert isinstance(a, Type) and isinstance(b, Type)
        self.a = a
        self.b = b
        self.constructors = OrderedDict({
            'Inl': a,
            'Inr': b,
        })

class Genredexpr__glob_red_flag(Record):
    '''
    type 'a glob_red_flag = {
        rBeta : bool;
        rMatch : bool;
        rFix : bool;
        rCofix : bool;
        rZeta : bool;
        rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
        rConst : 'a list
    }
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.fields = OrderedDict({
            'rBeta' : Bool(),
            'rMatch' : Bool(),
            'rFix' : Bool(),
            'rCofix' : Bool(),
            'rZeta' : Bool(),
            'rDelta' : Bool(),
            'rConst' : List(a),
        })


class Genredexpr__red_expr_gen(Variant):
    '''
    type ('a,'b,'c) red_expr_gen =
    | Red of bool
    | Hnf
    | Simpl of 'b glob_red_flag * ('b,'c) Util.union Locus.with_occurrences option
    | Cbv of 'b glob_red_flag
    | Cbn of 'b glob_red_flag
    | Lazy of 'b glob_red_flag
    | Unfold of 'b Locus.with_occurrences list
    | Fold of 'a list
    | Pattern of 'a Locus.with_occurrences list
    | ExtraRedExpr of string
    | CbvVm of ('b,'c) Util.union Locus.with_occurrences option
    | CbvNative of ('b,'c) Util.union Locus.with_occurrences option
    '''
    def __init__(self, a, b, c):
        assert isinstance(a, Type) and isinstance(b, Type) and isinstance(c, Type)
        self.a = a
        self.b = b
        self.c = c
        self.constructors = OrderedDict({
            'Simpl': Tuple(Genredexpr__glob_red_flag(b), 
                           Option(Locus__with_occurrences(Util__union(b, c)))),
            'Unfold': List(Locus__with_occurrences(b)),
        })


class Locus__hyp_location_flag(Variant):
    '''
    type hyp_location_flag = InHyp | InHypTypeOnly | InHypValueOnly
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'InHyp': None,
            'InHypTypeOnly': None,
            'InHypValueOnly': None,
        })


class Locus__hyp_location_expr(AliasType):
    '''
    type 'a hyp_location_expr = 'a with_occurrences * hyp_location_flag
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.alias = Tuple(Locus__with_occurrences(a), Locus__hyp_location_flag())


class Locus__clause_expr(Record):
    '''
    type 'id clause_expr =
        { onhyps : 'id hyp_location_expr list option;
            concl_occs : occurrences_expr }
    '''
    def __init__(self, id):
        assert isinstance(id, Type)
        self.id = id
        self.fields = OrderedDict({
            'onhyps': Option(List(Locus__hyp_location_expr(id))),
            'concl_occs': Locus__occurrences_expr(),
        })


# (** Possible arguments of a tactic definition *)

class Tacexpr__gen_tactic_arg(Variant):
    '''
    type 'a gen_tactic_arg =
    | TacGeneric     of 'lev generic_argument
    | ConstrMayEval  of ('trm,'cst,'pat) may_eval
    | Reference      of 'ref
    | TacCall    of ('ref * 'a gen_tactic_arg list) Loc.located
    | TacFreshId of string or_var list
    | Tacexp of 'tacexpr
    | TacPretype of 'trm
    | TacNumgoals

    constraint 'a = <
        term:'trm;
        dterm: 'dtrm;
        pattern:'pat;
        constant:'cst;
        reference:'ref;
        name:'nam;
        tacexpr:'tacexpr;
        level:'lev
    >
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'TacGeneric': Genarg__generic_argument(a.members['level']),
            'TacCall': Loc__located(Tuple(a.members['reference'], List(self))),
        })



class Tacexpr__advanced_flag(AliasType):
    '''
    type advanced_flag = bool  (* true = advanced         false = basic *)
    '''
    def __init__(self):
        self.alias = Bool()


class Tacexpr__evars_flag(AliasType):
    '''
    type evars_flag = bool     (* true = pose evars       false = fail on evars *)
    '''
    def __init__(self):
        self.alias = Bool()


class Tacexpr__clear_flag(AliasType):
    '''
    type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)
    '''
    def __init__(self):
        self.alias = Option(Bool())


class Tacexpr__with_bindings_arg(AliasType):
    '''
    type 'a with_bindings_arg = clear_flag * 'a with_bindings
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.alias = Tuple(Tacexpr__clear_flag(), Tactypes__with_bindings(a))


class Tacexpr__gen_atomic_tactic_expr(Variant):
    '''
    type 'a gen_atomic_tactic_expr =
    (* Basic tactics *)
    | TacIntroPattern of evars_flag * 'dtrm intro_pattern_expr CAst.t list
    | TacApply of advanced_flag * evars_flag * 'trm with_bindings_arg list *
        ('nam * 'dtrm intro_pattern_expr CAst.t option) option
    | TacElim of evars_flag * 'trm with_bindings_arg * 'trm with_bindings option
    | TacCase of evars_flag * 'trm with_bindings_arg
    | TacMutualFix of Id.t * int * (Id.t * int * 'trm) list
    | TacMutualCofix of Id.t * (Id.t * 'trm) list
    | TacAssert of
        evars_flag * bool * 'tacexpr option option *
        'dtrm intro_pattern_expr CAst.t option * 'trm
    | TacGeneralize of ('trm with_occurrences * Name.t) list
    | TacLetTac of evars_flag * Name.t * 'trm * 'nam clause_expr * letin_flag *
        intro_pattern_naming_expr CAst.t option

    (* Derived basic tactics *)
    | TacInductionDestruct of
        rec_flag * evars_flag * ('trm,'dtrm,'nam) induction_clause_list

    (* Conversion *)
    | TacReduce of ('trm,'cst,'pat) red_expr_gen * 'nam clause_expr
    | TacChange of 'pat option * 'dtrm * 'nam clause_expr

    (* Equality and inversion *)
    | TacRewrite of evars_flag *
        (bool * multi * 'dtrm with_bindings_arg) list * 'nam clause_expr *
        (* spiwack: using ['dtrm] here is a small hack, may not be
            stable by a change in the representation of delayed
            terms. Because, in fact, it is the whole "with_bindings"
            which is delayed. But because the "t" level for ['dtrm] is
            uninterpreted, it works fine here too, and avoid more
            disruption of this file. *)
        'tacexpr option
    | TacInversion of ('trm,'dtrm,'nam) inversion_strength * quantified_hypothesis

    constraint 'a = <
        term:'trm;
        dterm: 'dtrm;
        pattern:'pat;
        constant:'cst;
        reference:'ref;
        name:'nam;
        tacexpr:'tacexpr;
        level:'lev
    >
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'TacIntroPattern': Tuple(Tacexpr__evars_flag(), List(CAst__t(Tactypes__intro_pattern_expr(a.members['dterm'])))),
            'TacApply': Tuple(Tacexpr__advanced_flag(), Tacexpr__evars_flag(), 
                              List(Tacexpr__with_bindings_arg(a.members['term'])), 
                              Option(Tuple(a.members['name'], Option(CAst__t(Tactypes__intro_pattern_expr(a.members['dterm'])))))),
            'TacCase': Tuple(Tacexpr__evars_flag(), Tacexpr__with_bindings_arg(a.members['term'])),
            'TacReduce': Tuple(Genredexpr__red_expr_gen(a.members['term'], a.members['constant'], a.members['pattern']), 
                               Locus__clause_expr(a.members['name'])),
        })
        

class Tacexpr__gen_tactic_expr(Variant):
    '''
    and 'a gen_tactic_expr =
    | TacAtom of ('a gen_atomic_tactic_expr) Loc.located
    | TacThen of
        'a gen_tactic_expr *
        'a gen_tactic_expr
    | TacDispatch of
        'a gen_tactic_expr list
    | TacExtendTac of
        'a gen_tactic_expr array *
        'a gen_tactic_expr *
        'a gen_tactic_expr array
    | TacThens of
        'a gen_tactic_expr *
        'a gen_tactic_expr list
    | TacThens3parts of
        'a gen_tactic_expr *
        'a gen_tactic_expr array *
        'a gen_tactic_expr *
        'a gen_tactic_expr array
    | TacFirst of 'a gen_tactic_expr list
    | TacComplete of 'a gen_tactic_expr
    | TacSolve of 'a gen_tactic_expr list
    | TacTry of 'a gen_tactic_expr
    | TacOr of
        'a gen_tactic_expr *
        'a gen_tactic_expr
    | TacOnce of
        'a gen_tactic_expr
    | TacExactlyOnce of
        'a gen_tactic_expr
    | TacIfThenCatch of
        'a gen_tactic_expr *
        'a gen_tactic_expr *
        'a gen_tactic_expr
    | TacOrelse of
        'a gen_tactic_expr *
        'a gen_tactic_expr
    | TacDo of int or_var * 'a gen_tactic_expr
    | TacTimeout of int or_var * 'a gen_tactic_expr
    | TacTime of string option * 'a gen_tactic_expr
    | TacRepeat of 'a gen_tactic_expr
    | TacProgress of 'a gen_tactic_expr
    | TacShowHyps of 'a gen_tactic_expr
    | TacAbstract of
        'a gen_tactic_expr * Id.t option
    | TacId of 'n message_token list
    | TacFail of global_flag * int or_var * 'n message_token list
    | TacInfo of 'a gen_tactic_expr
    | TacLetIn of rec_flag *
        (lname * 'a gen_tactic_arg) list *
        'a gen_tactic_expr
    | TacMatch of lazy_flag *
        'a gen_tactic_expr *
        ('p,'a gen_tactic_expr) match_rule list
    | TacMatchGoal of lazy_flag * direction_flag *
        ('p,'a gen_tactic_expr) match_rule list
    | TacFun of 'a gen_tactic_fun_ast
    | TacArg of 'a gen_tactic_arg located
    | TacSelect of goal_selector * 'a gen_tactic_expr
    (* For ML extensions *)
    | TacML of (ml_tactic_entry * 'a gen_tactic_arg list) Loc.located
    (* For syntax extensions *)
    | TacAlias of (KerName.t * 'a gen_tactic_arg list) Loc.located

    constraint 'a = <
        term:'t;
        dterm: 'dtrm;
        pattern:'p;
        constant:'c;
        reference:'r;
        name:'n;
        tacexpr:'tacexpr;
        level:'l
    >
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'TacAtom': Loc__located(Tacexpr__gen_atomic_tactic_expr(a)),
            'TacThen': Tuple(self, self),
            'TacTry': self,
            'TacAlias': Loc__located(Tuple(Names__KerName__t(), List(Tacexpr__gen_tactic_arg(a)))), 
            'TacArg': Loc__located(Tacexpr__gen_tactic_arg(a)),
        })

class Evar_kinds__t(Variant):
    '''
    type t =
    | ImplicitArg of global_reference * (int * Id.t option)
        * bool (** Force inference *)
    | BinderType of Name.t
    | NamedHole of Id.t (* coming from some ?[id] syntax *)
    | QuestionMark of obligation_definition_status * Name.t
    | CasesType of bool (* true = a subterm of the type *)
    | InternalHole
    | TomatchTypeParameter of inductive * int
    | GoalEvar
    | ImpossibleCase
    | MatchingVar of matching_var_kind
    | VarInstance of Id.t
    | SubEvar of Evar.t
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'BinderType': Names__Name__t(),
        })

class Decl_kinds__binding_kind(Variant):
    '''
    type binding_kind = Explicit | Implicit
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Explicit': None,
            'Implicit': None,
        })

class Constr__case_style(Variant):
    '''
    type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle
    | RegularStyle (** infer printing form from number of constructor *)
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'LetStyle': None,
            'IfStyle': None,
            'LetPatternStyle': None,
            'MatchStyle': None,
            'RegularStyle': None,
        })

class Constrexpr__binder_kind(Variant):
    '''
    type binder_kind =
    | Default of binding_kind
    | Generalized of binding_kind * binding_kind * bool
        (** Inner binding, outer bindings, typeclass-specific flag
        for implicit generalization of superclasses *)
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Default': Decl_kinds__binding_kind(),
            'Generalized': Tuple(Decl_kinds__binding_kind(), Decl_kinds__binding_kind(), Bool()),
        })


class Constrexpr__proj_flag(AliasType):
    '''
    type proj_flag = int option (** [Some n] = proj of the n-th visible argument *)
    '''
    def __init__(self):
        self.alias = Option(Int())


class Constrexpr__instance_expr(AliasType):
    '''
    type instance_expr = Glob_term.glob_level list
    '''
    def __init__(self):
        self.alias = List(Glob_term__glob_level())


class Constrexpr__cases_pattern_expr_r(Variant):
    '''
    type cases_pattern_expr_r =
    | CPatAlias of cases_pattern_expr * lname
    | CPatCstr  of qualid
        * cases_pattern_expr list option * cases_pattern_expr list
    (** [CPatCstr (_, c, Some l1, l2)] represents [(@ c l1) l2] *)
    | CPatAtom of qualid option
    | CPatOr   of cases_pattern_expr list
    | CPatNotation of notation * cases_pattern_notation_substitution
        * cases_pattern_expr list (** CPatNotation (_, n, l1 ,l2) represents
                    (notation n applied with substitution l1)
                    applied to arguments l2 *)
    | CPatPrim   of prim_token
    | CPatRecord of (qualid * cases_pattern_expr) list
    | CPatDelimiters of string * cases_pattern_expr
    | CPatCast   of cases_pattern_expr * constr_expr
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'CPatAlias': Tuple(Constrexpr__cases_pattern_expr(), Names__lname()),
            'CPatCstr': Tuple(Libnames__qualid(), Option(List(Constrexpr__cases_pattern_expr())), List(Constrexpr__cases_pattern_expr())),
            'CPatAtom': Option(Libnames__qualid()),
            'CPatNotation': Tuple(Constrexpr__notation(), Constrexpr__cases_pattern_notation_substitution(), List(Constrexpr__cases_pattern_expr())),
            'CPatPrim': Constrexpr__prime_token(),
            'CPatRecord': List(Tuple(Libnames__qualid(), Constrexpr__cases_pattern_expr())),
            'CPatDelimiters': Tuple(String(), Constrexpr__cases_pattern_expr()),
        })


class Constrexpr__cases_pattern_expr(AliasType):
    '''
    and cases_pattern_expr = cases_pattern_expr_r CAst.t
    '''
    def __init__(self):
        if self.initialized:
            return
        self.alias = CAst__t(Constrexpr__cases_pattern_expr_r())


class Constrexpr__cases_pattern_notation_substitution(AliasType):
    '''
    and cases_pattern_notation_substitution =
        cases_pattern_expr list *     (** for constr subterms *)
        cases_pattern_expr list list  (** for recursive notations *)
    '''
    def __init__(self):
        if self.initialized:
            return
        self.alias = Tuple(List(Constrexpr__cases_pattern_expr()), List(List(Constrexpr__cases_pattern_expr())))


class Constrexpr__notation_key(AliasType):
    '''
    type notation_key = string
    '''
    inline = True

    def __init__(self):
        self.alias = String()

class Constrexpr__notation_entry_level(Variant):
    '''
    type notation_entry_level = InConstrEntrySomeLevel | InCustomEntryLevel of string * int
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'InConstrEntrySomeLevel': None,
            'InCustomEntryLevel': Tuple(String(), Int()),
        })

class Constrexpr__notation(AliasType):
    '''
    type notation = notation_entry_level * notation_key
    '''
    def __init__(self):
        self.alias = Tuple(Constrexpr__notation_entry_level(), Constrexpr__notation_key())


class Constrexpr__explicitation(Variant):
    '''
    type explicitation =
    | ExplByPos of int * Id.t option (* a reference to the n-th product starting from left *)
    | ExplByName of Id.t
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'ExplByPos': Tuple(Int(), Option(Names__Id__t())),
            'ExplByName': Names__Id__t(),
        })


class Constrexpr__sign(AliasType):
    '''
    type sign = bool
    '''
    def __init__(self):
        self.alias = Bool()


class Constrexpr__raw_natural_number(AliasType):
    '''
    type raw_natural_number = string
    '''
    def __init__(self):
        self.alias = Int()


class Constrexpr__prime_token(Variant):
    '''
    type prim_token =
    | Numeral of raw_natural_number * sign
    | String of string
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Numeral': Tuple(Constrexpr__raw_natural_number(), Constrexpr__sign()),
            'String': String(),
        })


class Constrexpr__constr_expr_r(Variant):
    '''
    and constr_expr_r =
    | CRef     of qualid * instance_expr option
    | CFix     of lident * fix_expr list
    | CCoFix   of lident * cofix_expr list
    | CProdN   of local_binder_expr list * constr_expr
    | CLambdaN of local_binder_expr list * constr_expr
    | CLetIn   of lname * constr_expr * constr_expr option * constr_expr
    | CAppExpl of (proj_flag * qualid * instance_expr option) * constr_expr list
    | CApp     of (proj_flag * constr_expr) *
                    (constr_expr * explicitation CAst.t option) list
    | CRecord  of (qualid * constr_expr) list

    (* representation of the "let" and "match" constructs *)
    | CCases of Constr.case_style   (* determines whether this value represents "let" or "match" construct *)
                * constr_expr option  (* return-clause *)
                * case_expr list
                * branch_expr list    (* branches *)

    | CLetTuple of lname list * (lname option * constr_expr option) *
                    constr_expr * constr_expr
    | CIf of constr_expr * (lname option * constr_expr option)
            * constr_expr * constr_expr
    | CHole   of Evar_kinds.t option * Namegen.intro_pattern_naming_expr * Genarg.raw_generic_argument option
    | CPatVar of Pattern.patvar
    | CEvar   of Glob_term.existential_name * (Id.t * constr_expr) list
    | CSort   of Glob_term.glob_sort
    | CCast   of constr_expr * constr_expr Glob_term.cast_type
    | CNotation of notation * constr_notation_substitution
    | CGeneralization of binding_kind * abstraction_kind option * constr_expr
    | CPrim of prim_token
    | CDelimiters of string * constr_expr
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'CRef': Tuple(Libnames__qualid(), Option(Constrexpr__instance_expr())),
            'CFix': Tuple(Names__lident(), List(Constrexpr__fix_expr())),
            'CCoFix': Tuple(Names__lident(), List(Constrexpr__cofix_expr())), 
            'CProdN': Tuple(List(Constrexpr__local_binder_expr()), Constrexpr__constr_expr()),
            'CLambdaN': Tuple(List(Constrexpr__local_binder_expr()), Constrexpr__constr_expr()),
            'CLetIn': Tuple(Names__lname(), Constrexpr__constr_expr(), Option(Constrexpr__constr_expr()), Constrexpr__constr_expr()),
            'CAppExpl': Tuple(Tuple(Constrexpr__proj_flag(), Libnames__qualid(), Option(Constrexpr__instance_expr())), List(Constrexpr__constr_expr())),
            'CApp': Tuple(Tuple(Constrexpr__proj_flag(), Constrexpr__constr_expr()), List(Tuple(Constrexpr__constr_expr(), Option(CAst__t(Constrexpr__explicitation()))))),
            'CCases': Tuple(Constr__case_style(), Option(Constrexpr__constr_expr()), List(Constrexpr__case_expr()), List(Constrexpr__branch_expr())), 
            'CLetTuple': Tuple(List(Names__lname()), Tuple(Option(Names__lname()), Option(Constrexpr__constr_expr())), Constrexpr__constr_expr(), Constrexpr__constr_expr()),
            'CIf': Tuple(Constrexpr__constr_expr(), Tuple(Option(Names__lname()), Option(Constrexpr__constr_expr())), Constrexpr__constr_expr(), Constrexpr__constr_expr()),
            'CHole': Tuple(Option(Evar_kinds__t()), Namegen__intro_pattern_naming_expr(), Option(Genarg__raw_generic_argument())),
            'CEvar': Tuple(Glob_term__existential_name(), List(Tuple(Names__Id__t(), Constrexpr__constr_expr()))),
            'CSort': Glob_term__glob_sort(),
            'CCast': Tuple(Constrexpr__constr_expr(), Glob_term__cast_type(Constrexpr__constr_expr())),
            'CNotation': Tuple(Constrexpr__notation(), Constrexpr__constr_notation_substitution()),
            'CPrim': Constrexpr__prime_token(),
            'CDelimiters': Tuple(String(), Constrexpr__constr_expr()),
        })


class Constrexpr__constr_expr(AliasType):
    '''
    and constr_expr = constr_expr_r CAst.t
    '''
    inline = True

    def __init__(self):
        if self.initialized:
            return
        self.alias = CAst__t(Constrexpr__constr_expr_r())


class Constrexpr__case_expr(AliasType):
    '''
    and case_expr = constr_expr                 (* expression that is being matched *)
                    * lname option                (* as-clause *)
                    * cases_pattern_expr option   (* in-clause *)
    '''
    def __init__(self):
        if self.initialized:
            return
        self.alias = Tuple(Constrexpr__constr_expr(), Option(Names__lname()), Option(Constrexpr__cases_pattern_expr()))


class Constrexpr__branch_expr(AliasType):
    '''
    and branch_expr =
        (cases_pattern_expr list list * constr_expr) CAst.t
    '''
    inline = True

    def __init__(self):
        if self.initialized:
            return
        self.alias = CAst__t(Tuple(List(List(Constrexpr__cases_pattern_expr())), Constrexpr__constr_expr()))

class Constrexpr__fix_expr(AliasType):
    '''
    and fix_expr =
        lident * (lident option * recursion_order_expr) *
        local_binder_expr list * constr_expr * constr_expr
    '''
    def __init__(self):
        if self.initialized:
            return
        self.alias = Tuple(Names__lident(), Tuple(Option(Names__lident()), Constrexpr__recursion_order_expr()), List(Constrexpr__local_binder_expr()), Constrexpr__constr_expr(), Constrexpr__constr_expr())


class Constrexpr__cofix_expr(AliasType):
    '''
    and cofix_expr =
        lident * local_binder_expr list * constr_expr * constr_expr
    '''
    def __init__(self):
        if self.initialized:
            return
        self.alias = Tuple(Names__lident(), List(Constrexpr__local_binder_expr()), Constrexpr__constr_expr(), Constrexpr__constr_expr())


class Constrexpr__recursion_order_expr(Variant):
    '''
    and recursion_order_expr =
    | CStructRec
    | CWfRec of constr_expr
    | CMeasureRec of constr_expr * constr_expr option (** measure, relation *)
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'CStructRec': None,
            'CWfRec': Constrexpr__constr_expr(),
            'CMeasureRec': Tuple(Constrexpr__constr_expr(), Option(Constrexpr__constr_expr())),
        })


class Constrexpr__constr_pattern_expr(AliasType):
    '''
    type constr_pattern_expr = constr_expr
    '''
    def __init__(self):
        self.alias = Constrexpr__constr_expr()


class Constrexpr__local_binder_expr(Variant):
    '''
    and local_binder_expr =
    | CLocalAssum   of lname list * binder_kind * constr_expr
    | CLocalDef     of lname * constr_expr * constr_expr option
    | CLocalPattern of (cases_pattern_expr * constr_expr option) CAst.t
    '''
    def  __init__(self):
        self.constructors = OrderedDict({
            'CLocalAssum': Tuple(List(Names__lname()), Constrexpr__binder_kind(), Constrexpr__constr_expr()),
            'CLocalPattern': CAst__t(Tuple(Constrexpr__cases_pattern_expr(), Option(Constrexpr__constr_expr())))
        })

class Constrexpr__constr_notation_substitution(AliasType):
    '''
    and constr_notation_substitution =
        constr_expr list *      (** for constr subterms *)
        constr_expr list list * (** for recursive notations *)
        cases_pattern_expr list *   (** for binders *)
        local_binder_expr list list (** for binder lists (recursive notations) *)
    '''
    def __init__(self):
        self.alias = Tuple(List(Constrexpr__constr_expr()), 
                           List(List(Constrexpr__constr_expr())),
                           List(Constrexpr__cases_pattern_expr()),
                           List(List(Constrexpr__local_binder_expr())))


class Names__module_ident(AliasType):
    '''
    type module_ident = Id.t
    '''
    def __init__(self):
        self.alias = Names__Id__t()


class Names__DirPath__t(Variant):
    '''
    type t = module_ident list
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_names.ml: type _dirpath = DirPath of Id.t list'
        self.constructors = OrderedDict({
            'DirPath': List(Names__Id__t()),
        }) 
  

class Names__MBId__t(Variant):
    '''
    type t = int * Id.t * DirPath.t
    '''
    def __init__(self):
        'coq-serapi/serlib/ser_names.ml: type _mbid = Mbid of Id.t * DirPath.t'
        self.constructors = OrderedDict({
            'Mbid': Tuple(Names__Id__t(), Names__DirPath__t()),
        })


class Names__Label__t(AliasType):
    '''
    type t = Id.t
    '''
    def __init__(self):
        self.alias = Names__Id__t()


class Names__ModPath__t(Variant):
    '''
    type t =
    | MPfile of DirPath.t
    | MPbound of MBId.t
    | MPdot of t * Label.t
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'MPfile': Names__DirPath__t(),
            'MPbound': Names__MBId__t(),
            'MPdot': Tuple(self, Names__Label__t())
        })


class Names__KerName__t(Variant):
    '''
      type t = {
        canary : Canary.t;
        modpath : ModPath.t;
        dirpath : DirPath.t;
        knlabel : Label.t;
        mutable refhash : int;
        (** Lazily computed hash. If unset, it is set to negative values. *)
    }
    '''
    def __init__(self):
       'coq-serapi/serlib/ser_names.ml: type _kername = Kername of ModPath.t * DirPath.t * Label.t'
       self.constructors = OrderedDict({
           'Kername': Tuple(Names__ModPath__t(), 
                            Names__DirPath__t(),
                            Names__Label__t())
       })


class Libnames__full_path(Record):
    '''
    type full_path = {
        dirpath : DirPath.t ;
        basename : Id.t }
    '''
    def __init__(self):
        self.fields = OrderedDict({
            'dirpath': Names__DirPath__t(),
            'basename': Names__Id__t(),
        }) 


class Libnames__qualid_r(Variant):
    '''
    type qualid_r = full_path
    '''
    def __init__(self):
        '''
        coq-serapi/serlib/ser_libnames.ml: 
        type _qualid =
            Ser_Qualid of Names.DirPath.t * Names.Id.t
        [@@deriving sexp]
        '''
        self.constructors = OrderedDict({
            'Ser_Qualid': Tuple(Names__DirPath__t(), Names__Id__t()),
        })


class Libnames__qualid(AliasType):
    '''
    type qualid = qualid_r CAst.t
    '''
    inline = True

    def __init__(self):
        self.alias = CAst__t(Libnames__qualid_r())


class Libnames__reference_r(Variant):
    '''
    type reference_r =
    | Qualid of qualid
    | Ident of Id.t
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Qualid': Libnames__qualid(),
            'Ident': Names__Id__t(),
        })


class Libnames__reference(AliasType):
    '''
    type reference = reference_r CAst.t
    '''
    inline = True

    def __init__(self):
        self.alias = CAst__t(Libnames__reference_r())


class Tacexpr__r_trm(AliasType):
    '''
    type r_trm = constr_expr
    '''
    def __init__(self):
        self.alias = Constrexpr__constr_expr()


class Tacexpr__r_pat(AliasType):
    '''
    type r_pat = constr_pattern_expr
    '''
    def __init__(self):
        self.alias = Constrexpr__constr_pattern_expr()


class Tacexpr__r_cst(AliasType):
    '''
    type r_cst = reference or_by_notation
    '''
    def __init__(self):
        self.alias = Constrexpr__or_by_notation(Libnames__reference())


class Tacexpr__r_ref(AliasType):
    '''
    type r_ref = reference
    '''
    def __init__(self):
        self.alias = Libnames__reference()


class Tacexpr__r_nam(AliasType):
    '''
    type r_nam = lident
    '''
    def __init__(self):
        self.alias = Names__lident()


class Tacexpr__r_lev(AliasType):
    '''
    type r_lev = rlevel
    '''
    def __init__(self):
        self.alias = Genarg__rlevel()


class Tacexpr__r_dispatch(UnimplementedType):
    '''
    type r_dispatch =  <
        term:r_trm;
        dterm:r_trm;
        pattern:r_pat;
        constant:r_cst;
        reference:r_ref;
        name:r_nam;
        tacexpr:raw_tactic_expr;
        level:rlevel
    >
    '''
    def __init__(self):
        self.members = OrderedDict({
            'term': Tacexpr__r_trm(),
            'dterm': Tacexpr__r_trm(),
            'pattern': Tacexpr__r_pat(),
            'constant': Tacexpr__r_cst(),
            'reference': Tacexpr__r_ref(),
            'name': Tacexpr__r_nam(),
            'level': Tacexpr__r_lev(),
        })


class Tacexpr__raw_tactic_expr(AliasType):
    '''
    and raw_tactic_expr =
        r_dispatch gen_tactic_expr
    '''
    def __init__(self):
        self.alias = Tacexpr__gen_tactic_expr(Tacexpr__r_dispatch())


class Genarg__genarg_val(Type):
    '''
    type 'l generic_argument = GenArg : ('a, 'l) abstract_argument_type * 'a -> 'l generic_argument
    '''
    def parsing_rules(self):
        raw_tacexpr = Tacexpr__raw_tactic_expr()
        ty = Genarg__genarg_type()
        list_val = NonEmptyList(self)
        opt_val = Option(self)
        pair_val = Tuple(self, self)
        return [
            list_val.nonterminal,
            opt_val.nonterminal,
            pair_val.nonterminal,
            '"(\\\"[XXX ser_gen]\\\" raw" %s ")"' % ty.nonterminal,  # default
            '"(\\\"[XXX ser_gen]\\\" glb" %s ")"' % ty.nonterminal,  # default
            '"(\\\"[XXX ser_gen]\\\" top" %s ")"' % ty.nonterminal,  # default
            Bool().nonterminal,
            Names__Id__t().nonterminal,
            raw_tacexpr.nonterminal,
        ], [list_val, opt_val, pair_val, raw_tacexpr, ty]


class Genarg__generic_argument(Variant):
    '''
    type 'l generic_argument = GenArg : ('a, 'l) abstract_argument_type * 'a -> 'l generic_argument
    '''
    def __init__(self, l):
        assert isinstance(l, Type)
        self.l = l

    def parsing_rules(self):
        'coq-serapi/serlib/ser_genarg.ml'
        if self.l.is_alias_for(Genarg__rlevel):
            level = 'raw'
        elif self.l.is_alias_for(Genarg__glevel):
            level = 'glb'
        else:
            assert self.l.is_alias_for(Genarg__tlevel)
            level = 'top'
        ty = Genarg__genarg_type()
        t = Genarg__genarg_val()
        return ['"(GenArg" "%s" %s %s ")"' % (level, ty.nonterminal, t.nonterminal)], [ty, t]


class Genarg__raw_generic_argument(AliasType):
    '''
    type raw_generic_argument = rlevel generic_argument
    '''
    def __init__(self):
        self.alias = Genarg__generic_argument(Genarg__rlevel())


class Vernacexpr__section_subset_expr(Variant):
    '''
    type section_subset_expr =
    | SsEmpty
    | SsType
    | SsSingl of lident
    | SsCompl of section_subset_expr
    | SsUnion of section_subset_expr * section_subset_expr
    | SsSubstr of section_subset_expr * section_subset_expr
    | SsFwdClose of section_subset_expr
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'SsEmpty': None,
            'SsType': None,
            'SsSingl': Names__lident(),
            'SsCompl': self,
            'SsUnion': Tuple(self, self),
            'SsSubstr': Tuple(self, self),
            'SsFwdClose': self,
        })


class Vernacexpr__opacity_flag(Variant):
    '''
    type opacity_flag   = Opaque | Transparent
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Opaque': None,
            'Transparent': None,
        })
 

class Names__Id__t(Type):
    '''
    type t = string
    '''
    inline = True

    def parsing_rules(self):
        #'coq-serapi/serlib/ser_names.ml'
        #rules, dependencies = String().parsing_rules()
        #return ['"(Id" %s ")"' % r for r in rules], dependencies
        return ['"(Id" /[^\)]+/ ")"'], []


class Names__Name__t(Variant):
    '''
    type t = Anonymous     (** anonymous identifier *)
    | Name of Id.t  (** non-anonymous identifier *)
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Anonymous': None,
            'Name': Names__Id__t(),
        })


class Names__lident(AliasType):
    '''
    type lident = Id.t CAst.t
    '''
    inline = True

    def __init__(self):
        self.alias = CAst__t(Names__Id__t())


class Names__lname(AliasType):
    '''
    type lname = Name.t CAst.t
    '''
    inline = True

    def __init__(self):
        self.alias = CAst__t(Names__Name__t())


class Glob_term__existential_name(AliasType):
    '''
    type existential_name = Id.t
    '''
    def __init__(self):
        self.alias = Names__Id__t()


# (** Sorts *)

class Glob_term__glob_sort_gen(Variant):
    '''
    type 'a glob_sort_gen =
    | GProp (** representation of [Prop] literal *)
    | GSet  (** representation of [Set] literal *)
    | GType of 'a (** representation of [Type] literal *)
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'GProp': None,
            'GSet': None,
            'GType': a,
        })


class Glob_term__sort_info(AliasType):
    '''
    type sort_info = (Libnames.qualid * int) option list
    '''
    def __init__(self):
        self.alias = List(Option(Tuple(Libnames__qualid(), Int())))
        #super().__init__()


class Glob_term__glob_sort(AliasType):
    '''
    type glob_sort = sort_info glob_sort_gen
    '''
    def __init__(self):
        self.alias = Glob_term__glob_sort_gen(Glob_term__sort_info())


# (** Casts *)

class Glob_term__cast_type(Variant):
    '''
    type 'a cast_type =
    | CastConv of 'a
    | CastVM of 'a
    | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)
    | CastNative of 'a
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'CastConv': a,
            'CastVM': a,
            'CastCoerce': None,
            'CastNative': a,
        })


class Glob_term__universe_kind(Variant):
    '''
    type 'a universe_kind =
    | UAnonymous
    | UUnknown
    | UNamed of 'a
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'UAnonymous': None,
            'UUnknown': None,
            'UNamed': a,
        })


class Glob_term__level_info(AliasType):
    '''
    type level_info = Libnames.qualid universe_kind
    '''
    def __init__(self):
        self.alias = Glob_term__universe_kind(Libnames__qualid())

class Glob_term__glob_level(AliasType):
    '''
    type glob_level = level_info glob_sort_gen
    '''
    def __init__(self):
        self.alias = Glob_term__glob_sort_gen(Glob_term__level_info())


# (** Bindings *) 

class Tactypes__quantified_hypothesis(Variant):
    '''
    type quantified_hypothesis = AnonHyp of int | NamedHyp of Id.t
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'AnonHyp': Int(),
            'NamedHyp': Names__Id__t(),       
        })


class Tactypes__explicit_bindings(AliasType):
    '''
    type 'a explicit_bindings = (quantified_hypothesis * 'a) CAst.t list
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.alias = List(CAst__t(Tuple(Tactypes__quantified_hypothesis(), a)))


class Tactypes__bindings(Variant):
    '''
    type 'a bindings =
    | ImplicitBindings of 'a list
    | ExplicitBindings of 'a explicit_bindings
    | NoBindings
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'ImplicitBindings': List(a),
            'ExplicitBindings': Tactypes__explicit_bindings(a),
            'NoBindings': None,
        })


# (** Introduction patterns *)

class Tactypes__intro_pattern_expr(Variant):
    '''
    type 'constr intro_pattern_expr =
    | IntroForthcoming of bool
    | IntroNaming of intro_pattern_naming_expr
    | IntroAction of 'constr intro_pattern_action_expr
    '''
    def __init__(self, constr):
        if self.initialized:
            return
        assert isinstance(constr, Type)
        self.constr = constr
        self.constructors = OrderedDict({
            'IntroForthcoming': Bool(),
            'IntroNaming': Namegen__intro_pattern_naming_expr(),
            'IntroAction': Tactypes__intro_pattern_action_expr(constr),
        })


class Namegen__intro_pattern_naming_expr(Variant):
    '''
    and intro_pattern_naming_expr =
    | IntroIdentifier of Id.t
    | IntroFresh of Id.t
    | IntroAnonymous
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'IntroIdentifier': Names__Id__t(),
            'IntroFresh': Names__Id__t(),
            'IntroAnonymous': None,
        })

class Tactypes__intro_pattern_action_expr(Variant):
    '''
    and 'constr intro_pattern_action_expr =
    | IntroWildcard
    | IntroOrAndPattern of 'constr or_and_intro_pattern_expr
    | IntroInjection of ('constr intro_pattern_expr) CAst.t list
    | IntroApplyOn of 'constr CAst.t * 'constr intro_pattern_expr CAst.t
    | IntroRewrite of bool
    '''
    def __init__(self, constr):
        assert isinstance(constr, Type)
        self.constr = constr
        self.constructors = OrderedDict({
            'IntroWildcard': None,
            'IntroOrAndPattern': Tactypes__or_and_intro_pattern_expr(constr),
            'IntroInjection': List(CAst__t(Tactypes__intro_pattern_expr(constr))),
            'IntroApplyOn': Tuple(CAst__t(constr), CAst__t(Tactypes__intro_pattern_expr(constr))),
            'IntroRewrite': Bool(),
        })


class Tactypes__or_and_intro_pattern_expr(Variant):
    '''
    and 'constr or_and_intro_pattern_expr =
    | IntroOrPattern of ('constr intro_pattern_expr) CAst.t list list
    | IntroAndPattern of ('constr intro_pattern_expr) CAst.t list
    '''
    def __init__(self, constr):
        assert isinstance(constr, Type)
        self.constr = constr
        self.constructors = OrderedDict({
            'IntroOrPattern': List(List(CAst__t(Tactypes__intro_pattern_expr(constr))))  
        })


class Tactypes__with_bindings(AliasType):
    '''
    type 'a with_bindings = 'a * 'a bindings
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.alias = Tuple(a, Tactypes__bindings(a))


class Constrexpr__or_by_notation_r(Variant):
    '''
    type 'a or_by_notation_r =
    | AN of 'a
    | ByNotation of (string * string option)
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'AN': a,
            'ByNotation': Tuple(String(), Option(String())),
        })


class Constrexpr__or_by_notation(AliasType):
    '''
    type 'a or_by_notation = 'a or_by_notation_r CAst.t
    '''
    inline = True

    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.alias = CAst__t(Constrexpr__or_by_notation_r(a))


class Misctypes__or_var(Variant):
    '''
    type 'a or_var =
    | ArgArg of 'a
    | ArgVar of lident
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.constructors = OrderedDict({
            'ArgArg': a,
            'ArgVar': Names__lident(),
        })

class Vernacexpr__proof_end(Variant):
    '''
    type proof_end =
    | Admitted
    (*                         name in `Save ident` when closing goal *)
    | Proved of opacity_flag * lident option
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Admitted': None,
            'Proved': Tuple(Vernacexpr__opacity_flag(), Option(Names__lident())),
        })


class Vernacexpr__bullet(Variant):
    '''
    type bullet =
    | Dash of int
    | Star of int
    | Plus of int
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'Dash': Int(), 
            'Star': Int(),
            'Plus': Int(),
        })


class Vernacexpr__extend_name(AliasType):
    '''
    type extend_name =
    (** Name of the vernac entry where the tactic is defined, typically found
        after the VERNAC EXTEND statement in the source. *)
    string *
    (** Index of the extension in the VERNAC EXTEND statement. Each parsing branch
        is given an offset, starting from zero. *)
    int
    '''
    def __init__(self):
        self.alias = Tuple(String(), Int())


class Vernacexpr__goal_selector(Variant):
    '''
    type goal_selector =
    | SelectNth of int
    | SelectList of (int * int) list
    | SelectId of Id.t
    | SelectAll
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'SelectNth': Int(),
            'SelectList': List(Tuple(Int(), Int())),
            'SelectId': Names__Id__t(),
            'SelectAll': None,
        })


class Vernacexpr__vernac_expr(Variant):
    '''
    type nonrec vernac_expr =

    | VernacLoad of verbose_flag * string
    (* Syntax *)
    | VernacSyntaxExtension of bool * (lstring * syntax_modifier list)
    | VernacOpenCloseScope of bool * scope_name
    | VernacDelimiters of scope_name * string option
    | VernacBindScope of scope_name * class_rawexpr list
    | VernacInfix of (lstring * syntax_modifier list) *
        constr_expr * scope_name option
    | VernacNotation of
        constr_expr * (lstring * syntax_modifier list) *
        scope_name option
    | VernacNotationAddFormat of string * string * string

    (* Gallina *)
    | VernacDefinition of (Decl_kinds.discharge * Decl_kinds.definition_object_kind) * name_decl * definition_expr
    | VernacStartTheoremProof of Decl_kinds.theorem_kind * proof_expr list
    | VernacEndProof of proof_end
    | VernacExactProof of constr_expr
    | VernacAssumption of (Decl_kinds.discharge * Decl_kinds.assumption_object_kind) *
        inline * (ident_decl list * constr_expr) with_coercion list
    | VernacInductive of cumulative_inductive_parsing_flag * Decl_kinds.private_flag * inductive_flag * (inductive_expr * decl_notation list) list
    | VernacFixpoint of Decl_kinds.discharge * (fixpoint_expr * decl_notation list) list
    | VernacCoFixpoint of Decl_kinds.discharge * (cofixpoint_expr * decl_notation list) list
    | VernacScheme of (lident option * scheme) list
    | VernacCombinedScheme of lident * lident list
    | VernacUniverse of lident list
    | VernacConstraint of glob_constraint list

    (* Gallina extensions *)
    | VernacBeginSection of lident
    | VernacEndSegment of lident
    | VernacRequire of
        reference option * export_flag option * reference list
    | VernacImport of export_flag * reference list
    | VernacCanonical of reference or_by_notation
    | VernacCoercion of reference or_by_notation *
        class_rawexpr * class_rawexpr
    | VernacIdentityCoercion of lident * class_rawexpr * class_rawexpr
    | VernacNameSectionHypSet of lident * section_subset_expr 

    (* Type classes *)
    | VernacInstance of
        bool * (* abstract instance *)
        local_binder_expr list * (* super *)
        typeclass_constraint * (* instance name, class name, params *)
        (bool * constr_expr) option * (* props *)
        hint_info_expr

    | VernacContext of local_binder_expr list

    | VernacDeclareInstances of
        (reference * hint_info_expr) list (* instances names, priorities and patterns *)

    | VernacDeclareClass of reference (* inductive or definition name *)

    (* Modules and Module Types *)
    | VernacDeclareModule of bool option * lident *
        module_binder list * module_ast_inl
    | VernacDefineModule of bool option * lident * module_binder list *
        module_ast_inl module_signature * module_ast_inl list
    | VernacDeclareModuleType of lident *
        module_binder list * module_ast_inl list * module_ast_inl list
    | VernacInclude of module_ast_inl list

    (* Solving *)

    | VernacSolveExistential of int * constr_expr

    (* Auxiliary file and library management *)
    | VernacAddLoadPath of rec_flag * string * DirPath.t option
    | VernacRemoveLoadPath of string
    | VernacAddMLPath of rec_flag * string
    | VernacDeclareMLModule of string list
    | VernacChdir of string option

    (* State management *)
    | VernacWriteState of string
    | VernacRestoreState of string

    (* Resetting *)
    | VernacResetName of lident
    | VernacResetInitial
    | VernacBack of int
    | VernacBackTo of int

    (* Commands *)
    | VernacCreateHintDb of string * bool
    | VernacRemoveHints of string list * reference list
    | VernacHints of string list * hints_expr
    | VernacSyntacticDefinition of lident * (Id.t list * constr_expr) *
        onlyparsing_flag
    | VernacDeclareImplicits of reference or_by_notation *
        (explicitation * bool * bool) list list
    | VernacArguments of reference or_by_notation *
        vernac_argument_status list (* Main arguments status list *) *
            (Name.t * vernac_implicit_status) list list (* Extra implicit status lists *) *
        int option (* Number of args to trigger reduction *) *
            [ `ReductionDontExposeCase | `ReductionNeverUnfold | `Rename |
            `ExtraScopes | `Assert | `ClearImplicits | `ClearScopes |
            `DefaultImplicits ] list
    | VernacArgumentsScope of reference or_by_notation *
        scope_name option list
    | VernacReserve of simple_binder list
    | VernacGeneralizable of (lident list) option
    | VernacSetOpacity of (Conv_oracle.level * reference or_by_notation list)
    | VernacSetStrategy of
        (Conv_oracle.level * reference or_by_notation list) list
    | VernacUnsetOption of export_flag * Goptions.option_name
    | VernacSetOption of export_flag * Goptions.option_name * option_value
    | VernacAddOption of Goptions.option_name * option_ref_value list
    | VernacRemoveOption of Goptions.option_name * option_ref_value list
    | VernacMemOption of Goptions.option_name * option_ref_value list
    | VernacPrintOption of Goptions.option_name
    | VernacCheckMayEval of Genredexpr.raw_red_expr option * goal_selector option * constr_expr
    | VernacGlobalCheck of constr_expr
    | VernacDeclareReduction of string * Genredexpr.raw_red_expr
    | VernacPrint of printable
    | VernacSearch of searchable * goal_selector option * search_restriction
    | VernacLocate of locatable
    | VernacRegister of lident * register_kind
    | VernacComments of comment list

    (* Proof management *)
    | VernacAbort of lident option
    | VernacAbortAll
    | VernacRestart
    | VernacUndo of int
    | VernacUndoTo of int
    | VernacBacktrack of int*int*int
    | VernacFocus of int option
    | VernacUnfocus
    | VernacUnfocused
    | VernacBullet of bullet
    | VernacSubproof of goal_selector option
    | VernacEndSubproof
    | VernacShow of showable
    | VernacCheckGuard
    | VernacProof of Genarg.raw_generic_argument option * section_subset_expr option
    | VernacProofMode of string
    (* Toplevel control *)
    | VernacToplevelControl of exn

    (* For extension *)
    | VernacExtend of extend_name * Genarg.raw_generic_argument list
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            #'VernacAddMLPath': Tuple(Bool(), String()),
            #'VernacChdir': Option(String()),
            'VernacEndProof': Vernacexpr__proof_end(),
            'VernacBullet': Vernacexpr__bullet(),
            'VernacFocus': Option(Int()),
            'VernacUnfocus': None,
            'VernacSubproof': Option(Vernacexpr__goal_selector()),
            'VernacEndSubproof': None,
            'VernacProof': Tuple(Option(Genarg__raw_generic_argument()), 
                                 Option(Vernacexpr__section_subset_expr())),
            'VernacExtend': Tuple(Vernacexpr__extend_name(), List(Genarg__raw_generic_argument())),
        })


class CAst__t(Record):
    '''
    type 'a t = {
        v   : 'a;
        loc : Loc.t option;
    }
    '''
    def __init__(self, a):
        assert isinstance(a, Type)
        self.a = a
        self.fields = OrderedDict({
            'v': a,
            'loc': Option(Loc__t()),
        })

    def parsing_rules(self):
        return ['"(" %s ")"' % self.fields['v'].nonterminal], [self.fields['v']]


class Vernacexpr__vernac_control(Variant):
    '''
    type vernac_control =
    | VernacExpr of vernac_flag list * vernac_expr
    (* boolean is true when the `-time` batch-mode command line flag was set.
        the flag is used to print differently in `-time` vs `Time foo` *)
    | VernacTime of bool * vernac_control CAst.t
    | VernacRedirect of string * vernac_control CAst.t
    | VernacTimeout of int * vernac_control
    | VernacFail of vernac_control
    '''
    def __init__(self):
        self.constructors = OrderedDict({
            'VernacExpr': Tuple(List(Vernacexpr__vernac_flag()), Vernacexpr__vernac_expr()),
            #'VernacTime': Tuple(Bool(), CAst__t(self)),
            #'VernacRedirect': Tuple(String(), CAst__t(self)),
            #'VernacTimeout': Tuple(Int(), self),
            #'VernacFail': self,
        })


class Loc__located(Type):
    '''
    type 'a located = t option * 'a
    '''
    def __init__(self, t):
        assert isinstance(t, Type)
        self.t = t

    def parsing_rules(self):
        return Tuple(Option(Loc__t()), self.t).parsing_rules()


class Serapi__CoqAst(Variant):
    def __init__(self):
        self.constructors = OrderedDict({
            'CoqAst': Loc__located(Vernacexpr__vernac_control()),
        })


if __name__ == '__main__':
    t1 = Serapi__CoqAst()
    print(t1.to_ebnf(recursive=True))
    #print(t2.parsing_rules())
    #print(t3.parsing_rules())
