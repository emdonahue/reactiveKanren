"use strict"
import {logging, log, toString, copy, equals, is_string, is_number, is_boolean, is_pojo, assert} from './util.js';
//TODO global generic 'model' variable object as a shortcut for (v,m) => v.eq(m), maybe generalize to path vars
//TODO let query variables be added manually not just extracted from fresh
//TODO use clone node over create element for speed when applicable (eg dynamic model)
//TODO look into event delegation
//TODO can we generalize LCS to use partial reuse instead of binary equality
//TODO reuse old node even on new template in case it has some common sub templates (eg can reuse a text node we are about to throw away just by textContent =)
//TODO rewrite entire mk engine to be non recursive to handle large cases
//TODO for an iterable, create an entire subtree with all sub-iterables generating only 1 copy, then clone that node and reuse it across all subsequent iterations
//TODO give lvar an .orderby method that constructs a view ordered by whatever that binds to. then even if its bound multiply we just produce sibling dynamic sets ordered by different fns
//TODO dont have to pass mvar anymore with lexical scope

//diffing
//if dynamic nodes are unsorted, then we know that they can only insert or remove, not reorder? no, the model might change
//check out https://github.com/facebook/react/issues/10382
//if only additions, no diffing needed. if only deletions, no diffing needed.
//cloning only makes sense if templates arent recursive, so is there a way to check/annotate that? maybe recursiveness could trigger more advanced diffing, since each subtree may have to trash the previous structurally distinct subtree. alternatively, maybe we only clone the parent stump and then children overwrite the placeholders (can use comments or text nodes as placeholders, and then if the placeholder turns out to be a text node, we're already done, otherwise we just sacrifice a textnode

//TODO implement property list dom nodes
//TODO implement iterable children of dom nodes
//TODO implement static var children of dom nodes
//TODO implement dynamic properties as children of dom nodes

// TYPES

function is_text(x) { return is_string(x) || is_number(x) || is_boolean(x); }

// APP INTERFACE
class RK {
    constructor(template, data) {
        this.mvar = new SVar().name('model');
        this.substitution = this.mvar.set(data).reunify_substitution(nil);
        this.template = (template instanceof Function) ? template(this.mvar) : template;
        this.child = View.render(this.substitution, this, this.template);
    }
    root() { return this.child.root(); }
    rerender(g) {
        if (g instanceof Function) return this.rerender(g(this.mvar));
        this.substitution = g.reunify_substitution(this.substitution);
        log('rerender', this.constructor.name, toString(this.substitution));
        this.child = this.child.rerender(this.substitution, this);
        return this;
    }
    toString() { return `(RK ${this.child})` }}



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
    extend(k, v) { //TODO make a separate filter(remove) based extend for reactive
        return this.filter(x => x.car != k).acons(k, v);
    }
    member(e) {
        return this.memp((x) => x == e);
    }
    assoc(key) {
        let self = this;
        while (self instanceof Pair) {
            if (self.car instanceof Pair && self.car.car === key) return self.car;
            self = self.cdr;
        }
        return false;
    }
    sort(f) { return list(...this.toArray().sort(f)); }
    static repeat(n, f) {
        return nil.repeat(n, f);
    }
    isFailure() { return false; }
    repeat(n, f) {
        if (n <= 0) return this;
        return this.cons(f()).repeat(n-1, f);
    }
    join(sep='') {
        let self = this, str = '', first = true;
        while (self instanceof Pair) {
            str += first ? self.car : sep + self.car;
            first = false;
            self = self.cdr; }
        return str; }
    filter(p) {
        let self = this, head = null, tail = null;
        while (self instanceof Pair) {
            if (p(self.car)) {
                if (!head)  tail = head = new Pair(self.car, null);
                else tail = tail.cdr = new Pair(self.car, null); }
            self = self.cdr; }
        if (tail) tail.cdr = self;
        else head = self;
        return head;
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
    walk_var(lvar) { return this.walk_binding(lvar).car; }
    reify(lvar) {
        if (arguments.length == 0) return this.map((b) => new Pair(b.car, this.reify(b.cdr))); //TODO make this its own debug thing?
        let v = this.walk(lvar);
        if (v instanceof LVar || primitive(v)) return v;
        if (v instanceof QuotedVar) return this.reify(v.lvar);
        if (v instanceof Pair) return new Pair(this.reify(v.car), this.reify(v.cdr));
        if (Array.isArray(v)) return v.map(e => this.reify(e));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v)]));
    }
    rereify(_lvar, mvars) {
        let {car: lvar, cdr: val} = this.walk_binding(_lvar);
        if (mvars.has(lvar)) return lvar;
        if (val instanceof LVar || primitive(val)) return val;
        if (Array.isArray(v)) return v.map(e => this.reify(e));
        return Object.assign(Object.create(Object.getPrototypeOf(val)), (Object.fromEntries(Object.entries(val).map(([k,v]) => [k, this.reify(v)]))));
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
        let x, y;
        ({car: x_var, cdr: x} = this.walk_binding(x_var));
        ({car: y_var, cdr: y} = this.walk_binding(y_var));
        log('unify', x_var, x, y_var, y);
        if (x === y) {
            if (x instanceof LVar || x_var === y_var) return this; // Vars already in same equivalence class: share lowest variable or just ground terms.
            else if (x_var instanceof LVar) return this.extend(x_var, y_var); // Align vars to same equivalence class
            else return this.extend(y_var, x_var); }
        if (x instanceof LVar) return this.extend(x, y_var); // Align to equivalence class, not bound value.
        if (y instanceof LVar) return this.extend(y, x_var);
        if (primitive(x) || primitive(y)) return failure; // Primitives but not ===
        if (Object.getPrototypeOf(x) !== Object.getPrototypeOf(y)) return failure;
        let s = this;
        for (let k of Object.keys(x).filter(k => Object.hasOwn(y, k))) {
            s = s.unify(x[k], y[k]);
            if (s.isFailure()) return failure;
        }
        return s;
    }
    update_binding(x, y, prev=nil, next=nil, updates=nil) { //TODO create an atomic quote wrapping form that prevents us from normalizing the substructure of a term, so we can decide where to let the system insert indirection
        if (primitive(x)) return this;
        let {car: x_var, cdr: x_val} = prev.walk_binding(x);

        //let {car: y_var, cdr: y_val} = prev.walk_binding(y);
        let y_val = prev.walk(y);
        /*
        if (next.assoc(x_var)) {
            y_val = next.assoc(x_var).cdr;
            log('reunify', 'subterm', x_var, y_val, next);
        }
        */
        log('reunify', 'lookup', x_var, x_val, y_val, prev);


        /*
        //if (next.assoc(y_var)) { //TODO need to walk repeatedly until exhausted
        let y_update = next.assoc(y_var);
        //log('reunify', 'occurs-check', 'x_var', x_var, 'y_var', y_var, 'y_update', y_update, 'occurs', occurs_check(x_var, y_var, prev), 'prev', prev);
        if (y_update && occurs_check(x_var, y_var, prev)) {
            log('reunify', 'occurs', 'x_var', x_var, 'y_var', y_var, 'y_val', y_val, 'y_update', y_update.cdr, 'curr', this, 'updates', updates);
            y_val = prev.walk(y_update.cdr);
            updates = updates.remove(y_update);
        }

        if (x_val instanceof QuotedVar && !(y_val instanceof QuotedVar)) {
            return this.update_binding(x_val.lvar, y_val, prev, next, updates);
        }
        */

        // Old prim values dont need to be reconciled, so just create new storage and update the new value.
        if (primitive(y_val) || y_val instanceof QuotedVar) {
            log('reunify', 'y prim', x_var, y_val);
            return updates.update_substitution(this.extend(x_var, y_val), prev, next); }

        else { // If old and new are objects, update the properties that exist and allocate new storage for those that don't.
            let norm = copy(y_val); //TODO should be type of y_val
            if (!primitive(x_val) && !(x_val instanceof LVar)) Object.assign(norm, x_val);

            for (let k in y_val) { // For each attr of the new value,
                if (!primitive(x_val) && !(x_val instanceof LVar) && Object.hasOwn(x_val, k)) { // if it already exists in the target, merge those bindings.
                    //s = s.update_binding(x_val[k], y_val[k], prev, next);
                    updates = updates.acons(x_val[k], y_val[k]);
                }
                else { // Otherwise, allocate new memory for the new values.
                    norm[k] = new SVar();
                    updates = updates.acons(norm[k], y_val[k]);
                    //s = s.update_binding(norm[k], y_val[k], prev, next);
                }
            }
            log('reunify', 'complex', x_var, norm);
            return updates.update_substitution(this.extend(x_var, norm), prev, next); //TODO we dont have to extend if we don't add any properties
        }
    }
    equiv_svars(v) { // Find all svars that point to the same svar as v in this substitution.
        let equiv = this.filter(b => b.cdr === v).map(b => this.equiv_svars(b.car)).fold((x,y) => x.append(y), nil)
        if (v instanceof SVar) return equiv.cons(v);
        return equiv;
    }
    repatch(patch) {
        return patch.fold((s, p) => s.rebind(p.car, p.cdr), this);
    }
    rebind(x, y) {
        log('reunify', 'rebind', x, y);
        if (y instanceof LVar) return this;
        if (primitive(y)) return this.extend(x, y); // x is a model var so no need for walk_binding: no indirection
        let x_val = this.walk(x);
        let self = this;
        let normalized = Object.create(Object.getPrototypeOf(y)); // type y but properties x_val
        if (!(primitive(x_val) || x_val instanceof LVar)) {
            Object.assign(normalized, x_val); // assign existing properties in case y doesn't overwrite
            
        }
        for (let k in y) {
            if (!(primitive(x_val) || x_val instanceof LVar) && Object.hasOwn(x_val, k)) self = self.rebind(normalized[k], y[k]);
            else self = self.rebind(normalized[k] = new SVar(), y[k]);
        }
        return self.extend(x, normalized);
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
    firstAnswer() { return this.car.substitution; }
    memp(p) {
        if (p(this.car)) return this.car;
        return this.cdr.memp(p);
    }
    remove(x) {
        if (this.car == x) return this.cdr;
        return this.cdr.remove(x).cons(this.car);
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
    update_substitution(curr, prev=curr, next=this) { // Called on the updates substitution with the normal substitution as a parameter.
        log('reunify', 'update_substitution', toString(curr));
        return curr.update_binding(this.caar(), this.cdar(), prev, next, this.cdr);
    }
    every(f) {
        f(this.car);
        this.cdr.every(f);
        return this; }
    isNil() { return false; }

    // x->1, y->2


    _toString() {
        window.lst = this; //TODO remove tostring debugging reference
        return `${toString(this.car)}${this.cdr instanceof Pair ? ' ' : ''}${this.cdr instanceof List ? this.cdr._toString() : ' . ' + toString(this.cdr)}`;
    }
}

class Empty extends List {
    toArray() {
        return [];
    }

    memp(p) { return undefined; };
    map(f) { return this; };
    update_substitution(s) { return s; }
    append(xs) { return xs; }
    isNil() { return true; }
    fold(f, x) { return x; }
    remove(x) { return this; }
    firstAnswer() { return failure; }
    every(f) { return this; }
    _toString() { return ''; }
}

function cons(...xs) { return xs.reduceRight((x,y) => new Pair(y, x)); }

function list(...xs) { return cons(...xs, nil); }

// Vars & Data
class LVar {
    static id = 0;
    constructor(name='') {
	this.id = LVar.id++;
        this.label = name;
    }
    toString() {
        return `<${this.label}${this.label ? ':' : ''}${this.id}>`;
    }
    unify(x) {
        return new Unification(this, x);
    }
    eq(x) { return this.unify(i); }
    eq(x) { return this.unify(x); }
    set(x) { return new Reunification(this, x); }
    name(n) { this.label = n; return this; }
    quote() { return new QuotedVar(this); }
    constraint(f, ...lvars) { return new Constraint(f, this, ...lvars); }
    isStringo() { return this.constraint(v => is_string(v)); }
    isNumbero() { return this.constraint(v => is_number(v)); }
    isPairo() { return this.constraint(v => v instanceof Pair); }
    isNotPairo() { return this.constraint(v => !(v instanceof Pair)); }
    membero(x) { return fresh((a,b) => [this.eq(cons(a,b)), conde(a.eq(x), b.membero(x))]); }
    leafo(x) { return conde([this.isNotPairo(), this.eq(x)],
                            [fresh((a,b) => [this.eq(cons(a,b)), conde(a.leafo(x), b.leafo(x))])]); }
    imembero(x,o,n=0) { return fresh((a,b) => [this.eq(cons(a,b)), conde([a.eq(x), o.eq(n)], b.imembero(x,o,n+1))]); } //TODO make imembero accept ground order terms
    tailo(x) { return conde([this.eq(nil), x.eq(this)], fresh((a,d) => [this.eq(cons(a,d)), d.tailo(x)])) };
}

class SVar extends LVar {
    toString() { return `[${this.label}${this.label ? ':' : ''}${this.id}]`; }
}

class QuotedVar {
    constructor(lvar) {
        this.lvar = lvar;
    }
    toString() { return `"${this.lvar}"`; };
}

// Goals
function primitive(x) {
    return is_string(x) || is_boolean(x) || is_number(x) || x === nil || x === null || x === undefined || x instanceof Function;
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
    conde(...g) {
        return conde(this, ...g);
    }
    filter(f) { return f(this) ? this : succeed; }
    run(n=-1, {reify=nil, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => reify ? log('run', 'reify', s.substitution.reify(reify)) : s);

    }
    expand_run(s=nil, v=[]) { //TODO remove default viewleaf
        return this.expand(new State(s), succeed, succeed, v);
    }
    reunify_substitution(sub) {
        let r = this.run(-1, {reify: false, substitution: sub});
        let updates = r.map(st => st.reify_updates()).fold((ups, up) => up.append(ups), nil); //TODO may need to walk_binding the reunifications so theyre not dependent on transient state that will be thrown away. also, what happens if setting free vars?
        log('reunify', 'updates', updates, sub);
        return updates.update_substitution(sub);
    }
    cont(s) { return s.isFailure() ? failure : this.eval(s); }
    expand_ctn(s, cjs, v) {
        log('expand', 'ctn', this+'', cjs, toString(s?.substitution));
        return s.isFailure() ? v(cjs.conj(this)) : this.expand(s, succeed, cjs, v); }
    suspend(s) { return new Suspended(s, this) }
    apply(sub) { return sub.isFailure() ? failure : this.run(1, {reify: false, substitution: sub}).firstAnswer(); }
    is_disj() { return false; }
    rediff(sub) {
        // get [mvar, value, sub] pairs, then reify each value in sub skipping mvars
        let answers = this.run(-1, {reify: false, substitution: sub}).map(a => ({answer: a, updates: a.reactive_updates()}));
        let mvars = answers.fold((mvars, u) => u.updates.fold((mvars, u) => mvars.add(u.car), mvars), new Set());
        let reified = answers.map(a => a.updates.map(u => cons(u.car, a.answer.substitution.rereify(u.cdr, mvars)))).fold((p, u) => p.append(u), nil);
        return reified;
        
    }
    toString() { return JSON.stringify(this); }
}

class Succeed extends Goal {
    eval(s) { return s; }
    suspend(s, ctn=succeed) { return ctn.cont(s); }
    cont(s) { return s; }
    expand_ctn(s, cjs, [...args]) {
        log('expand', 'return', this+'', cjs, s.substitution+'');
        return AnswerView.render(cjs, s.substitution, ...args);
    }
    conj(g) { return g; }
    expand(s, ctn, cjs, v) { return s.expand_ctn(ctn, cjs, v); }
    toString() { return 'succeed'; }
}

class Fail extends Goal {
    eval(s) { return failure; }
    suspend(s) { return failure; }
    conj(g) { return fail; }
    expand(s, ctn, cjs, v) {
        log('expand', 'fail', cjs.conj(ctn));
        return new FailureView(cjs.conj(ctn)); }
    toString() { return 'fail'; }
}

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        assert(lhs, rhs);
        this.lhs = lhs;
        this.rhs = rhs;
    }
    filter(f) { return this.lhs.filter(f).conj(this.rhs.filter(f)); }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, this.rhs.conj(ctn));
    }
    expand(s, ctn, cjs, v) {
        log('expand', 'conj', this+'', ctn, cjs);
        return this.lhs.expand(s, this.rhs.conj(ctn), cjs, v);
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
    expand(s, ctn, cjs, v) {
        log('expand', 'disj', this+'', ctn, cjs);
        return new CondeView(this.lhs.expand(s, ctn, succeed, v), this.rhs.expand(s, ctn, succeed, v), cjs);
    }
    toString() { return `(${this.lhs} | ${this.rhs})`; }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=-1, {reify=this.vars, ...rest}={}) { return super.run(n, {reify: reify, ...rest}); }
    eval(s, ctn=succeed) {
        return this.instantiate().conj(ctn).suspend(s);
    }
    expand(s, ctn, cjs, v) {
        return this.instantiate().expand(s, ctn, cjs, v);
    }
    instantiate() { return to_goal(this.ctn(...this.vars)); }
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
    expand(s, ctn, cjs, v) {
        log('expand', '==', this+'', ctn+'', cjs);
        s = s.unify(this.lhs, this.rhs);
        return s.expand_ctn(ctn, cjs.conj(this), v);
    }
    toString() { return `(${toString(this.lhs)} == ${toString(this.rhs)})`; }
}

class Constraint extends Goal {
    constructor(f, ...lvars) {
        super();
        this.lvars = [...lvars];
        this.f = f;
    }
    eval(s, ctn=succeed) {
        if (this.f.apply(null, this.lvars.map(x => s.walk(x)))) return ctn.cont(s);
        return failure;
    }
    expand(sub, ctn, cjs, v) {
        let s = (this.f.apply(null, this.lvars.map(x => sub.walk(x)))) ? sub : failure;
        log('expand', 'constraint', this+'', ctn, cjs, toString(sub?.substitution), s);
        return s.expand_ctn(ctn, cjs.conj(this), v);
    }
    toString() { return `${this.f}(${this.lvars})`; }
}

class Reunification extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    toString() { return `(${toString(this.lhs)} =!= ${toString(this.rhs)})`; }
    eval(s, ctn=succeed) { return ctn.cont(s.update(this.lhs, this.rhs)); }
}

function conde(...condes) {
    return condes.reduceRight((cs, c) => to_goal(c).disj(cs), fail);
}

function conj(...conjs) {
    return conjs.reduceRight((cs, c) => to_goal(c).conj(cs), succeed);
}

function unify(x, y) {
    return new Unification(x, y);
}

function reunify(x, y) {
    return new Reunification(x, y);
}

function to_goal(g) {
    if (Array.isArray(g)) return g.reduceRight((cs, c) => to_goal(c).conj(to_goal(cs)));
    else if (true === g) return succeed;
    else if (!g) return fail;
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
        if (0 === n || n === -5) return nil; //TODO remove -50 emergency recursion stop
        let s = this;
        while (s.isIncomplete()) { s = s.step(); }
        if (failure == s) return nil;
        log('run', 'take', s.answer());
        return new Pair(s.answer(), s.step().take(n-1));
    }
    isIncomplete() { return true; }
    isFailure() { return false; }
}

class Failure extends Stream {
    unify() { return this; };
    reify(x) { return x; };
    eval(x) { return this; };
    mplus(s) { return s; };
    _mplus(s) { return s; };
    isIncomplete() { return false; }
    step() { return this; }
    isFailure() { return true; }
    expand_ctn(ctn, cjs, rtrn) { return new FailureView(cjs.conj(ctn)); }
}

class State extends Stream {
    constructor(sub=nil, updates=nil) {
        super();
        assert(sub instanceof List);
        this.substitution = sub;
        this.updates = updates;
    }
    take(n) { return list(this); }
    reify(x) { return this.substitution.reify(x); }
    unify(x, y) {
        let s = this.substitution.unify(x, y);
        log('unify', x, y, toString(this.substitution), '->', s);
        if (s == failure) return s;
        return new State(s, this.updates); }
    reify_updates() {
        return this.updates.map(u =>
            this.substitution.equiv_svars(this.walk_binding(u.car).car).map(v => cons(v, this.reify_update(u.cdr, this.walk_binding(u.car).car))))
            .fold((x,y) => x.append(y), nil); }
    reify_update(lvar, parent) {
        let {car: vr, cdr: v} = this.substitution.walk_binding(lvar);
        log('reunify', 'skipreify', parent, lvar, vr, v);
        if (vr != parent && occurs_check(parent, vr, this.substitution) && this.updates.assoc(vr)) {
            return this.reify_update(this.updates.assoc(vr).cdr, parent);
        }
        if (v instanceof LVar || primitive(v)) return v;
        if (v instanceof QuotedVar) return this.reify(v.lvar);
        if (v instanceof Pair) return new Pair(this.reify(v.car), this.reify(v.cdr));
        if (Array.isArray(v)) return v.map(e => this.reify(e));
        return Object.fromEntries(Object.entries(v).map(([k,v]) => [k, this.reify(v)]));
    }
    reactive_updates() {
        return this.updates.map(u => cons(this.substitution.walk_var(u.car), u.cdr));
    }
    patch(mvars) {
        //let diff = this.updates.map(u => this.substitution.);
        //return mvars;
    }
    update(x, y) {
        return new State(this.substitution, this.updates.acons(x, y)); }
    extend(x, y) { return new State(this.substitution.extend(x, y), this.updates); }
    eval(g) { return g.eval(this); }
    isIncomplete() { return false; }
    answer() { return this; }
    step() { return failure; }
    mplus(s) { return new Answers(this, s); }
    _mplus(s) { return new Answers(this, s); }
    walk_binding(lvar) { return this.substitution.walk_binding(lvar); }
    walk(lvar) { return this.substitution.walk(lvar); }
    expand_ctn(ctn, cjs, rtrn) { return ctn.expand_ctn(this, cjs, rtrn); }
}


function descendant_order(x,y,s) { // Descendants go first, so -1 if x is a descendant of y
    if (occurs_check(y, x, s)) return -1; //TODO delete fn
    else if (occurs_check(x, y, s)) return 1;
    return 0;
}

function occurs_check(x,y,s) { // Check if y occurs in x
    if (primitive(x)) return false;

    else if (!(x instanceof LVar)) {
        for (let k in x) {
            if (occurs_check(x[k], y, s)) return true;
        }
    }
    else if (x == y) return true;
    let b = s.assoc(x);
    if (b) return occurs_check(b.cdr,y,s);
    return false;
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

// DOM

class View {
    static render(sub, app, template) {
        assert(template, app instanceof RK);
        if (is_text(template)) return TextView.render(template);
        else if (Array.isArray(template)) return NodeView.render(sub, app, template);
        else return GoalView.render(sub, app, template); }}


class GoalView { //Replaces a child template and generates one sibling node per answer, with templates bound to the view var.
    constructor(vvar, ovar, child, comment=document.createComment('')) {
        assert(comment instanceof Node);
        this.vvar = vvar; // Bound to view templates of each child
        this.ovar = ovar; // Bound to order key of each child
        this.child = child; //Root of tree of views
        this.comment = comment; // Attached to DOM as placeholder if all children fail
    }
    static render(sub, app, template) {
        assert(template, app instanceof RK);
        if (template instanceof LVar) return this.render_lvar(sub, app, template);
        else if (template instanceof Function) return this.render_f(sub, app, template);
        else throw Error(template);
    }
    
    static render_lvar(sub, app, template) {
        log('render', this.name, 'lvar', template, toString(sub));
        return new this(template, null, AnswerView.render(succeed, sub, template, app)); }
    
    static render_f(sub, app, f) {
        assert(app instanceof RK)
        let v = new LVar('view').name('view'), o = new LVar().name('order'), g = to_goal(f(v, o)); // Since o takes up second slot, there's no good api for binding f to 'this' for recursive anonymous functions
        log('render', this.name, 'f', g, toString(sub));
        return log('render', this.name + '^', toString(sub), new this(v, o, g.expand_run(sub, [v, app]))); }
    
    root() {
        let r = this.child.root();
        if (r instanceof DocumentFragment && !r.childNodes.length) return this.comment;
        return r; }
    sortfn() { return (a,b) => a.order == b.order ? 0 : a.order < b.order ? -1 : 1; }
    subviews(child=this.child) { return child.items().sort(this.sortfn()); }
    rerender(sub, app) {
        log('rerender', this.constructor.name, toString(sub));
        let add = [], del = [], nochange = [];

        this.child.firstNode()?.before(this.comment);
        //this.child = this.child.rerender(sub, mvar, this.vvar, add, del, nochange);
        [this.child,] = this.child.rerender(sub, app, this.vvar, this.comment);
        //if (!add.length && !nochange.length) this.child.firstNode().before(this.comment); // Comment placeholder not needed if a real node is in the dom
        //if (add.length || nochange.length) this.comment.remove();
        if (this.child.firstNode()) this.comment.remove();

        for (let item of del) item.remove();
        return this; }

    remove() { this.child.remove(); }
    items(a=[]) {
        this.child.items(a);
        return a; }
    firstNode() { return this.child.firstNode(); }
    lastNode() { return this.child.lastNode(); }
    toString() { return `(root ${this.child})`}}

class CondeView {
    constructor(lhs, rhs, goal) {
        this.goal = goal;
        this.lhs = lhs;
        this.rhs = rhs; }
    root(fragment=document.createDocumentFragment()) {
        this.lhs.root(fragment);
        this.rhs.root(fragment);
        return fragment; }
    remove() {
        this.lhs.remove();
        this.rhs.remove(); }
    toArray(a) {
        this.lhs.toArray(a);
        this.rhs.toArray(a);
        return a; }
    rerender(sub, app, vvar, nodecursor) {
        sub = this.goal.apply(sub);
        assert(!sub.isFailure());
        [this.lhs,nodecursor] = this.lhs.rerender(sub, app, vvar, nodecursor);
        [this.rhs,nodecursor] = this.rhs.rerender(sub, app, vvar, nodecursor);
        return [this, nodecursor];
    }
    items(a=[]) {
        this.lhs.items(a);
        this.rhs.items(a);
        return a; }
    firstNode() { return this.lhs.firstNode() ?? this.rhs.firstNode(); }
    lastNode() { return this.rhs.lastNode() ?? this.lhs.lastNode(); }
    asGoal() { return this.goal.conj(this.lhs.asGoal().disj(this.rhs.asGoal())); }
    toString() { return `(conde ${this.goal} ${this.lhs} ${this.rhs})`; }}

class FailureView { // Failures on the initial render that may expand to leaves or branches.
    constructor(goal) {
        this.goal = goal; }
    items(a=[]) { return a; }
    firstNode() { return null; }
    lastNode() { return null; }
    root(fragment=document.createDocumentFragment()) { return fragment; }
    rerender(sub, app, vvar, nodecursor) {
        let expanded = this.goal.expand_run(sub, [vvar, app]);
        if (expanded instanceof this.constructor) return [expanded, nodecursor];
        nodecursor.after(expanded.root());
        return [expanded, expanded.lastNode()];
    }
    toString() { return `(fail ${this.goal})`; }}

class FailedAnswerView { // Rerender failures of atomic leaves that may cache nodes
    constructor(child) {
        this.child = child; }
    items(a=[]) { return a; }
    firstNode() { return null; } // Prevents dynamic nodes from inserting anchors on a node not in the dom
    lastNode() { return null; }
    rerender(sub, app, vvar, nodecursor) {
        let [c,nextcursor] = this.child.rerender(sub, app, vvar, nodecursor);
        if (c instanceof this.constructor) return [c, nodecursor];
        nodecursor.after(c.root()); // Normally items would not make changes to dom, so add in items that were previously removed.
        return [c, nextcursor]; 
    }
    root (fragment=document.createDocumentFragment()) { return fragment; }
    toString() { return `(fail ${this.child})`; }}

class AnswerView { // Displayable iterable item
    constructor(goal, template=null, child=null, order=null) {
        this.goal = goal;
        if (template instanceof LVar) throw Error(template);
        this.child = child;
        this.template = template;
        this.order = order; }
    static render(goal, sub, vvar, app, ovar) {
        assert(app instanceof RK)
        log('render', this.name, sub?.reify(vvar), vvar+'', goal+'', toString(sub));
        if (!sub) return new FailureView(goal);
        let template = sub.walk(vvar);
        assert(!(template instanceof List), !(template instanceof LVar));
        return new this(goal, template, View.render(sub, app, template), ovar); }
    rerender(sub, app, vvar, nodecursor) {
        sub = this.goal.apply(sub);
        if (sub.isFailure()) return [new FailedAnswerView(this.remove()), nodecursor];
        log('rerender', this.constructor.name, vvar, sub.walk(vvar), toString(sub));
        assert(!(sub.walk(vvar) instanceof List), !(sub.walk(vvar) instanceof LVar));
        this.child = this.child.rerender(sub, app, sub.walk(vvar));
        return [this, this.lastNode()];
    }
    root(fragment) {
        log('root', this.constructor.name, fragment);
        if (fragment) fragment.append(this.child.root());
        else return this.child.root(); }
    key() { return this.template; }
    remove() {
        this.child.remove();
        return this; }
    firstNode() { return this.child.firstNode(); }
    lastNode() { return this.child.lastNode(); }
    items(a=[]) {
        a.push(this);
        return a; }
    toArray(a) { a.push(this); return a; }
    toString() { return this.goal.toString(); }}


class NodeView { 
    constructor(template, children, node) {
        this.template = template;
        this.node = node;
        this.children = children; }

    static render(sub, app, template) {
        log('render', this.name, template, sub);
        let children = [];
        let node = this.render_node(template, sub, app, children);
        log('render', this.name + '^', children);
        return new this(template, children, node);
    }
    static render_node([tparent, ...tchildren], sub, app, children) {
        let parent = this.render_parent(tparent, sub, app, children);
        this.render_children(parent, [...tchildren], sub, app, children);
        return parent;
    }
    static render_parent(tparent, sub, app, children) {
        if (is_string(tparent)) return this.render_parent({tagName: tparent});
        if (tparent instanceof LVar) return this.render_parent(sub.walk(tparent), sub, children);
        let parent = document.createElement(tparent.tagName ?? 'div');
        for (let k in tparent) {
            log('render', 'attr', parent, k, tparent[k]);
            if (k === 'tagName') continue;
            else if (k.substr(0,2) === 'on') children.push(EventView.render(sub, parent, k.substr(2), to_goal(tparent[k]), app));
            else if (is_text(tparent[k])) parent[k] = tparent[k];
            else children.push(AttrView.render(sub, parent, k, tparent[k]));
        }
        return parent;
    }
    static render_children(parent, tchildren, sub, app, children) {
        log('render', this.name, 'children', parent, tchildren);
        for (let tchild of tchildren) {
            this.render_child(parent, tchild, sub, app, children); }
    }
    static render_child(parent, tchild, sub, app, children) {
        log('render', this.name, 'child', parent, tchild);
        if (is_text(tchild)) parent.append(tchild);
        else if (Array.isArray(tchild)) parent.append(this.render_node(tchild, sub, app, children));
        else {
            children.push(GoalView.render(sub, app, tchild));
            parent.append(children[children.length-1].root()); }}
    
    rerender(sub, app, template=this.template) {
        log('rerender', this.constructor.name, template, this.template, equals(template, this.template), this.children, toString(sub));
        if (!equals(template, this.template)) {
            let v = View.render(sub, app, template); //TODO thread app
            this.node.replaceWith(v.root());
            return v; }
        for (let i in this.children) this.children[i] = this.children[i].rerender(sub, app);
        return this;
    }
    root() { return this.node; }
    remove() { if (this.node) this.node.remove(); }
    firstNode() { return this.node; }
    lastNode() { return this.node; }}

class TextView {
    constructor(template, node) {
        this.template = template;
        this.node = node; }
    static render(template) {
        return new this(template, document.createTextNode(template));
    }
    rerender(sub, app, template=this.template) {
        log('rerender', this.constructor.name, template, this.template);
        if (is_text(template)) {
            if (this.template !== template) {
                this.template = template;
                this.node.textContent = template; }
            return this; }
        return View.render(sub, app, template); //TODO thread app
    }
    root() {
        log('root', this.constructor.name, this.template);
        assert(this.node.textContent === this.template);
        return this.node; }
    remove() { if (this.node) this.node.remove(); }
    firstNode() { return this.node; }
    lastNode() { return this.node; }}

class AttrView {
    constructor(node, attr, goal, vvar) {
        this.node = node;
        this.attr = attr; //TODO if attr is tagName, generate new node, swap children, and swap into dom
        this.goal = goal;
        this.vvar = vvar;
    }
    static render(sub, node, attr, val) {        
        log('render', this.name, toString(sub));
        if (val instanceof LVar) return this.render_lvar(sub, node, attr, val);
        else if (val instanceof Function) this.render_f(sub, node, attr, val);
        else throw Error(val);
    }
    static render_lvar(sub, node, attr, val) {
        node[attr] = sub.walk(val);
        return new this(node, attr, succeed, val);
    }
    static render_f(sub, node, attr, val) {
        let v = new LVar(), g = val(v);
        let vals = g.run(-1, {reify: v, substitution: sub});
        if (!vals.isNil()) node[attr] = vals.join(' ');
        return new this(node, attr, g, v);
    }
    rerender(sub, app) {
        return this;
    }
}

class EventView {
    constructor(sub, node, event, handler) {
        
    }
    static render(sub, node, event, handler, app) {
        //TODO should run in its own sub and apply changes to main sub
        node.addEventListener(event, e => app.rerender(handler instanceof Goal ? handler : to_goal(handler(e))));
        return new this();
    }
    rerender() { return this; }
}


function view(template) { return new Template(template); }

export {RK, nil, cons, list, List, Pair, LVar, primitive, succeed, fail, fresh, conde, unify, reunify, failure, Goal, quote, QuotedVar, conj, SVar, view};
