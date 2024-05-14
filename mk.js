import {logging, log, dlog, toString, copy, equals} from './util.js';

// Lists
class List {
    static fromTree(a) {
        return list(...a).map(x => Array.isArray(x) ? this.fromTree(x) : x);
    }
    [Symbol.iterator]() {
        return this.toArray()[Symbol.iterator]();
    }
    length() {
        return this.toArray().length;
    }
    cons(e) {
        return new Pair(e, this);
    }
    acons(k, v) {
        return this.cons(new Pair(k, v));
    }
    extend(k, v) {
        return this.filter(x => x.car != k).acons(k, v);
    }
    member(e) {
        return this.memp((x) => x == e);
    }
    static repeat(n, f) {
        return nil.repeat(n, f);
    }
    repeat(n, f) {
        if (n <= 0) return this;
        return this.cons(f()).repeat(n-1, f);
    }
    walk(lvar) {
        if (!(lvar instanceof LVar)) return lvar;
        const v = this.assoc(lvar);
        if (v) { return this.walk(v.cdr); }
        else return lvar;
    }
    walk_binding(lvar) {
        if (!(lvar instanceof LVar)) return new Pair(lvar, lvar);
        const v = this.assoc(lvar);
        if (v) { return (v.cdr instanceof LVar) ? this.walk_binding(v.cdr) : v; }
        else return new Pair(lvar, lvar);
    }
    reify(lvar) {
        if (arguments.length == 0) return this.map((b) => new Pair(b.car, this.reify(b.cdr)));
        let v = this.walk(lvar);
        if (v instanceof LVar || primitive(v)) return v;
        if (v instanceof Pair) return new Pair(this.reify(v.car), this.reify(v.cdr));
        if (Array.isArray(v)) return v.map(e => this.reify(e));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v)]));
    }
    walk_path(lvar, prop, ...path) {
        let v = this.walk(lvar);
        if (path.length == 0) return v[prop];
        return this.walk_path(v[prop], ...path);
    }
    toString() {
        return '(' + this._toString() + ')';
    }    
    unify(x_var, y_var) { //DOC unifier has to be very lazy about preserving variable paths and not updating to latest value
        let x = this.walk(x_var);
        let y = this.walk(y_var);
        log('unify', x, y);
        if (x == y) return this;
        if (x instanceof LVar) return this.extend(x, y_var);
        if (y instanceof LVar) return this.extend(y, x_var);
        if (primitive(x) || primitive(y)) return failure;
        let s = this;
        for (let k of Object.keys(x).filter(k => Object.hasOwn(y, k))) {
            s = s.unify(x[k], y[k]);
            if (s === failure) return failure;
        }
        return s;
    }
}

class Pair extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
    caar() { return this.car.car; }
    cdar() { return this.car.cdr; }
    toArray() {
        return [this.car].concat((this.cdr instanceof List) ? this.cdr.toArray() : [this.cdr]);            
    }
    assoc(key) {
        if (this.car instanceof Pair && this.car.car == key) {
            return this.car;
        }
        else {
            return this.cdr.assoc(key);
        }
    }
    memp(p) {
        if (p(this.car)) return this.car;
        return this.cdr.memp(p);
    }
    filter(p) {
        if (p(this.car)) return this.cdr.filter(p).cons(this.car);
        return this.cdr.filter(p);
    }
    map(f) {
        return this.cdr.map(f).cons(f(this.car));
    }
    fold(f, x) {
        return this.cdr.fold(f, f(x, this.car));
    }
    append(xs) {
        return new Pair(this.car, this.cdr.append(xs));
    }
    update_substitution(s2, s=s2) { // Called on the updates substitution with the normal substitution as a parameter.
        return this.cdr.update_substitution(s2.update_binding(this.caar(), this.cdar(), s), s);
    }
    
    update_binding(x, y, sub) {        
        if (primitive(x)) return this;
        let {car: x_var, cdr: x_val} = sub.walk_binding(x);
        let {car: y_var, cdr: y_val} = sub.walk_binding(y);
        log('reunify', 'lookup', x_var, x_val, y_var, y_val, sub);
        
        if (x_val instanceof QuotedVar && !(y_val instanceof QuotedVar)) {
            return this.update_binding(x_val.lvar, y_val, sub);
        }

        /*
        else if (primitive(x_val)) { // New prim values can just be dropped in over top of old values.
            let [n, s] = normalize(y_val, this);
            log('reunify', 'x prim', x_var, n);
            if (!primitive(y_val)) s = this.update_binding();
            return s.extend(x_var, n);
        }
        */

        // Old prim values dont need to be reconciled, so just create new storage and update the new value.
        else if (primitive(y_val) || y_val instanceof QuotedVar) {
            log('reunify', 'y prim', x_var, y_val);
            return this.extend(x_var, y_val); }

        else { // If old and new are objects, update the properties that exist and allocate new storage for those that don't.
            let norm = copy(y_val); //TODO should be type of y_val
            if (!primitive(x_val)) Object.assign(norm, x_val);
            let s = this;
            let n;
            for (let k in y_val) { // For each attr of the new value,
                if (!primitive(x_val) && Object.hasOwn(x_val, k)) { // if it already exists in the target, merge those bindings.
                    s = s.update_binding(x_val[k], y_val[k], sub);
                    //norm[k] = _val[k];
                }
                else { // Otherwise, allocate new memory for the new values.
                    //[n, s] = normalize(y_val[k], s);
                    norm[k] = new LVar();
                    s = s.update_binding(norm[k], y_val[k], sub);
                }
            }
            log('reunify', 'complex', x_var, norm);
            return s.extend(x_var, norm); //TODO we dont have to extend if we don't add any properties
        }
    }
    _toString() {
        return `${toString(this.car)}${this.cdr instanceof Pair ? ' ' : ''}${this.cdr instanceof List ? this.cdr._toString() : ' . ' + toString(this.cdr)}`;
    }
}

class Empty extends List {
    toArray() {
        return [];
    }
    
    assoc(key) {
        return false;
    }
    memp(p) { return undefined; };
    filter(p) { return this; };
    map(f) { return this; };
    update_substitution(s) { return s; }
    update_binding(x, y) { return this.extend(x, y); }
    append(xs) { return xs; }
    fold(f, x) { return x; }
    _toString() { return ''; }
}

function cons(...xs) { return xs.reduceRight((x,y) => new Pair(y, x)); }

function list(...xs) { return cons(...xs, nil); }

// Vars & Data
class LVar {
    static id = 0;
    constructor() {
	this.id = LVar.id++;
        this.label = '';
    }
    toString() {
        return `<${this.label}${this.label ? ':' : ''}${this.id}>`;
    }
    unify(x) {
        return new Unification(this, x);
    }
    eq(x) { return this.unify(x); }
    set(x) { return new UnifyUpdate(this, x); }
    name(n) { this.label = n; return this; }
    quote() { return new QuotedVar(this); }
}

class QuotedVar {
    constructor(lvar) {
        this.lvar = lvar;
    }
    toString() { return `"${this.lvar}"`; };
}

// Goals
function primitive(x) {
    return typeof x == 'string' || typeof x == 'boolean' || typeof x == 'number' || x === nil || x === null || x === undefined;
}

class Goal {
    conj(x) {
        if (succeed === x) return this;
        if (fail === x) return fail;
        return new Conj(this, x);
    }
    disj(x) {
        if (fail === x) return this;
        return new Disj(this, x);
    }
    filter(f) { return f(this) ? this : succeed; }
    run(n=1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => s.update_substitution()).map(s => reify ? s.reify(nil) : s);
        
    }
    cont(s) { return s === failure ? failure : this.eval(s); }
    suspend(s) { return new Suspended(s, this) }
    is_disj() { return false; }
    toString() { return JSON.stringify(this); }
}

class Succeed extends Goal {
    eval(s) { return s; }
    suspend(s, ctn=succeed) { return ctn.cont(s); }
    cont(s) { return s; }
    conj(g) { return g; }
    toString() { return 'succeed'; }
}

class Fail extends Goal {
    eval(s) { return failure; }
    suspend(s) { return failure; }
    conj(g) { return fail; }
    toString() { return 'fail'; }
}

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    filter(f) { return this.lhs.filter(f).conj(this.rhs.filter(f)); }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, this.rhs.conj(ctn));
    }
    toString() { return `(${this.lhs} & ${this.rhs})`; }
}

class Disj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    is_disj() { return true; }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, ctn).mplus(this.rhs.eval(s, ctn));
    }
    toString() { return `(${this.lhs} | ${this.rhs})`; }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => s.update_substitution()).map(s => reify ? log('run', s.substitution).reify(this.vars) : s);
    }
    eval(s, ctn=succeed) {
        return to_goal(this.ctn(...this.vars)).conj(ctn).suspend(s);
    }
    toString() { return `(fresh ${this.vars} ${this.ctn})`; }
}

class Unification extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s, ctn=succeed) {
        return ctn.cont(s.unify(this.lhs, this.rhs));
    }
    toString() { return `(${toString(this.lhs)} == ${toString(this.rhs)})`; }
}

class UnifyUpdate extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    toString() { return `(${toString(this.lhs)} =!= ${toString(this.rhs)})`; }
    eval(s, ctn=succeed) { return ctn.cont(s.update(this.lhs, this.rhs)); }
}

class Reunification extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s, ctn=succeed) { return ctn.cont(s.extend(this.lhs, this.rhs)); }
}

function conde(...condes) {
    return condes.reduceRight((cs, c) => to_goal(c).disj(to_goal(cs)));
}

function unify(x, y) {
    return new Unification(x, y);
}

function reunify(x, y) {
    return new Reunification(x, y);
}

function setunify(x, y) {
    return new UnifyUpdate(x, y);
}

function to_goal(g) {
    if (Array.isArray(g)) return g.reduceRight((cs, c) => to_goal(c).conj(to_goal(cs)));
    else if (true === g) return succeed;
    else if (false === g) return fail;
    else return g;
}

function fresh(f) {
    return new Fresh(List.repeat(f.length, () => new LVar()), f);
}

function quote(q) {
    return new QuotedVar(q);
}

// Streams
class Stream {
    mplus(s) { return s._mplus(this); }
    _mplus(s) { return new MPlus(this, s); }
    take(n) {
        let s = this;
        while (s.isIncomplete()) { s = s.step(); }
        if (failure == s) return nil;
        return new Pair(s.answer(), s.step().take(n-1));
    }
    isIncomplete() { return true }
}

class Failure extends Stream {
    unify() { return this };
    reify(x) { return x };
    eval(x) { return this };
    mplus(s) { return s };
    _mplus(s) { return s };
    isIncomplete() { return false }
    step() { return this }
}

class State extends Stream {
    constructor(sub=nil, updates=nil) {
        super();
        this.substitution = sub;
        this.updates = updates;
    }
    take(n) { return list(this); }
    reify(x) { return this.substitution.reify(x); }
    unify(x, y) {
        let s = this.substitution.unify(x, y);
        log('unify', x, y, this.substitution, '->', s);
        if (s == failure) return s;
        return new State(s, this.updates); }
    update(x, y) {
        return new State(this.substitution, this.updates.acons(x, y)); }
    extend(x, y) { return new State(this.substitution.extend(x, y), this.updates); }
    eval(g) { return g.eval(this); }
    isIncomplete() { return false; }
    answer() { return this; }
    step() { return failure; }
    mplus(s) { return new Answers(this, s); }
    _mplus(s) { return new Answers(this, s); }
    update_substitution() {
        log('update_substitution', this.substitution, this.updates);
        let s = new State(this.updates.update_substitution(this.substitution));
        log('updated_substitution', s.substitution);
        return s;
    }
}

class Suspended extends Stream {
    constructor(s, g) {
        super();
        this.state=s;
        this.goal = g;
    }
    step() { return this.goal.eval(this.state); }
}

class Answers extends Stream {
    constructor(state, stream) {
        super();
        this.state = state;
        this.stream = stream;
    }
    isIncomplete() { return false; }
    answer() { return this.state; }
    step() { return this.stream; }
    mplus(s) { return new Answers(this.state, this.stream.mplus(s)); }
    _mplus(s) { return new Answers(this.state, this.stream.mplus(s)); }
}

class MPlus extends Stream {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    step() {
        return this.lhs.step().mplus(this.rhs);
    }
}

// Constants
const nil = new Empty();
const fail = new Fail;
const succeed = new Succeed;
const failure = new Failure;

// RRP

function normalize(model, sub=nil) {
    if (primitive(model) || model instanceof QuotedVar) return [model, sub];
    else if (model instanceof LVar) return new LVar();
    else if (Array.isArray(model)) { return normalize(list(...model), sub); }
    else {
        let m = Object.create(Object.getPrototypeOf(model));
        let n;
        for (let k in model) {
            if ((model[k] instanceof LVar)) {
                m[k] = new LVar();
                sub = sub.extend(m[k], sub.walk(model[k])); }
            else {
                let v = new LVar();
                [n,sub] = normalize(model[k], sub);
                sub = sub.extend(v, n);
                m[k] = v;
            }
        }
        return [m, sub];
    }
}

export {nil, cons, list, List, Pair, LVar, primitive, succeed, fail, fresh, conde, unify, setunify, normalize, reunify, failure, Goal, quote};
