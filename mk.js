"use strict"
import {logging, log, dlog, toString, copy, equals, is_string, is_number, is_boolean, is_pojo} from './util.js';
//TODO global generic 'model' variable object as a shortcut for (v,m) => v.eq(m), maybe generalize to path vars
//TODO let query variables be added manually not just extracted from fresh
//TODO use clone node over create element for speed when applicable (eg dynamic model)
//TODO look into event delegation
//TODO can we generalize LCS to use partial reuse instead of binary equality
//TODO reuse old node even on new template in case it has some common sub templates (eg can reuse a text node we are about to throw away just by textContent =)


// APP INTERFACE
class RK {
    constructor(template, data) {
        this.template = template;
        this.mvar = new LVar().name('base model');
        this.substitution = nil.extend(this.mvar, data); }
    render() {
        this.view = render(this.template, this.substitution, this.mvar);
        return this.view.render(); }}

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
    sort(f) { return list(...this.toArray().sort(f)); }
    static repeat(n, f) {
        return nil.repeat(n, f);
    }
    isFailure() { return false; }
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
        if (v instanceof QuotedVar) return this.reify(v.lvar);
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
        let s = this;
        for (let k of Object.keys(x).filter(k => Object.hasOwn(y, k))) {
            s = s.unify(x[k], y[k]);
            if (s.isFailure()) return failure;
        }
        return s;
    }
    update_binding(x, y, prev=nil, next=nil, updates=nil) {
        if (primitive(x)) return this;
        let {car: x_var, cdr: x_val} = prev.walk_binding(x);

        let {car: y_var, cdr: y_val} = prev.walk_binding(y);
        /*
        if (next.assoc(x_var)) {
            y_val = next.assoc(x_var).cdr;
            log('reunify', 'subterm', x_var, y_val, next);
        }
        */
        log('reunify', 'lookup', x_var, x_val, y_var, y_val, prev);


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
    firstAnswer() { return this.car.substitution; }
    memp(p) {
        if (p(this.car)) return this.car;
        return this.cdr.memp(p);
    }
    filter(p) {
        if (p(this.car)) return this.cdr.filter(p).cons(this.car);
        return this.cdr.filter(p);
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
        return curr.update_binding(this.caar(), this.cdar(), prev, next, this.cdr);
    }
    every(f) {
        f(this.car);
        this.cdr.every(f);
        return this; }
    isNil() { return false; }

    // x->1, y->2


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
    eq(x) { return this.unify(i); }
    eq(x) { return this.unify(x); }
    set(x) { return new Reunification(this, x); }
    name(n) { this.label = n; return this; }
    quote() { return new QuotedVar(this); }
    constraint(f, ...lvars) { return new Constraint(f, this, ...lvars); }
    isStringo() { return this.constraint(v => is_string(v)); }
    isNumbero() { return this.constraint(v => is_number(v)); }
    isPairo() { return this.constraint(v => v instanceof Pair); }
    membero(x) { return fresh((a,b) => [this.eq(cons(a,b)), conde(a.eq(x), b.membero(x))]); }
    imembero(x,o,n=0) { return fresh((a,b) => [this.eq(cons(a,b)), conde([a.eq(x), o.eq(n)], b.imembero(x,o,n+1))]); } //TODO make imembero accept ground order terms
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
    filter(f) { return f(this) ? this : succeed; }
    run(n=-1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => reify ? s.reify(nil) : s);

    }
    expand_run(s=nil, v=((g,s) => IterableViewItem.render(g, s, v, null))) { //TODO remove default viewleaf
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
        log('expand', 'ctn', this, cjs, s);
        return s.isFailure() ? v(cjs.conj(this)) : this.expand(s, succeed, cjs, v); }
    suspend(s) { return new Suspended(s, this) }
    apply(sub) { return sub.isFailure() ? failure : this.run(1, {reify: false, substitution: sub}).firstAnswer(); }
    is_disj() { return false; }
    toString() { return JSON.stringify(this); }
}

class Succeed extends Goal {
    eval(s) { return s; }
    suspend(s, ctn=succeed) { return ctn.cont(s); }
    cont(s) { return s; }
    expand_ctn(s, cjs, v) {
        log('expand', 'return', this, cjs, s);
        return v(cjs,s.substitution);
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
        return v(cjs.conj(ctn)); }
    toString() { return 'fail'; }
}

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        if (!lhs || !rhs) throw new Error('Conj takes 2 arguments' + lhs + rhs);
        this.lhs = lhs;
        this.rhs = rhs;
    }
    filter(f) { return this.lhs.filter(f).conj(this.rhs.filter(f)); }
    eval(s, ctn=succeed) {
        return this.lhs.eval(s, this.rhs.conj(ctn));
    }
    expand(s, ctn, cjs, v) {
        log('expand', 'conj', this, ctn, cjs);
        return this.lhs.expand(s, ctn.conj(this.rhs), cjs, v);
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
        log('expand', 'disj', this, ctn, cjs);
        return new IterableViewBranch(this.lhs.expand(s, ctn, succeed, v), this.rhs.expand(s, ctn, succeed, v), cjs);
    }
    toString() { return `(${this.lhs} | ${this.rhs})`; }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=-1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => reify ? log('run', 'reify', s.substitution.reify(this.vars)) : s);
    }
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
        log('expand', '==', this, ctn, cjs);
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
    expand(s, ctn, cjs, v) {
        log('expand', 'constraint', this, ctn, cjs);
        s = (this.f.apply(null, this.lvars.map(x => s.walk(x)))) ? s : failure;
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
    expand_ctn(ctn, cjs, rtrn) { return rtrn(cjs.conj(ctn)); }
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

function render(tmpl, sub=nil, model=null) {
    log('parse', tmpl, toString(sub));
    if (is_string(tmpl) || is_number(tmpl)) return new ViewTextNode(tmpl); // Simple Text nodes
    /*
    else if (tmpl instanceof LVar) { // Build a dynamic node keyed to a single static model var
        log('render', 'var', tmpl);
        return DynamicNode.render(tmpl, sub, obs, model, update, goals); }*/
    else if (tmpl instanceof Template) return tmpl.render(sub, model);
    else if (tmpl instanceof Function) return IterableViewRoot.render(tmpl, sub, model); // Build a dynamic node using the model

    //else if (tmpl instanceof LVar) { return render(sub.walk(tmpl), sub, model); }
    else if (Array.isArray(tmpl)) return render_head(tmpl, sub, model);
    else {
        console.error('Unrecognized render template', tmpl); //TODO remove debug print when done developing
        throw Error('Unrecognized render template: ' + toString(tmpl)); }}

function render_head([tmpl_head, ...tmpl_children], sub, model) {
    log('render', 'head', tmpl_head, tmpl_children);
    if (is_string(tmpl_head)) return render_head([{tagName: tmpl_head}, ...tmpl_children], sub, model);
    else if (is_pojo(tmpl_head)) return new ViewDOMNode(tmpl_head, tmpl_children.map(c => render(c, sub, model)));
    else throw Error('Unrecognized render head template: ' + toString(tmpl_head));
}


class View {
    update(s) {
        return this.rerender(s); }
    prerender() {
        let r = this.render();
        log('render', 'prerender', r.outerHTML ? r.outerHTML : r.textContent, this);
        return this; }}


class IterableViewRoot extends View { //Replaces a child template and generates one sibling node per answer, with templates bound to the view var.
    constructor(vvar, ovar, child, comment=document.createComment('')) {
        super();
        if (!(comment instanceof Node)) throw Error('comment not node')
        this.vvar = vvar; // Bound to view templates of each child
        this.ovar = ovar; // Bound to order key of each child
        this.child = child; //Root of tree of views
        this.comment = comment; // Attached to DOM as placeholder if all children fail
    }
    recreate(child) { return new this.constructor(this.vvar, this.ovar, child, this.comment); }
    sortfn() { return (a,b) => a.order == b.order ? 0 : a.order < b.order ? -1 : 1; }
    subviews(child=this.child) { return child.items().sort(this.sortfn()); }
    static render(f, sub, model) { //TODO can view vars all be the same physical var?
        let v = new LVar().name('view'), o = new LVar().name('order'), g = to_goal(f(v, model, o));
        log('parse', this.name, g, toString(sub));
        return new this(v, o, g.expand_run(sub, (g, s) => IterableViewItem.render(g, s, v, model,o))); }
    
    render() {
        let n, subviews = this.subviews();        
        if (!subviews.length) n = this.comment;
        else if (subviews.length === 1) n = subviews[0].render();
        else n = subviews.reduce((f,s) => f.appendChild(s.render()) && f, document.createDocumentFragment());
        log('render', this.constructor.name, n.outerHTML ? n.outerHTML : n.textContent, subviews);
        return n; }
    
    rerender(sub, model) {
        log('rerender', this.constructor.name, this, toString(sub), model+'');
        let subviews = this.subviews();
        let child = this.child.rerender(sub, model, this.vvar, this.ovar);
        let delta = this.subviews(child);
        log('rerender', this.constructor.name, 'delta', subviews, delta, child, toString(sub));

        if (!delta.length) subviews[0].firstNode().before(this.comment);
        this.diffDOM(this.buildLCSTable(subviews, delta), subviews, delta, sub, model);
        if (delta.length) this.comment.remove();
        //return new this.constructor(this.vvar, this.ovar, child, this.comment);
        return this.recreate(child);
    }

    buildLCSTable(subviews, delta) { // Build dynamic table for longest common subsequence problem. Reuse all the already in-DOM nodes possible by finding the greatest subsequence common to the previous and next timesteps.
        let lcs = [...new Array(subviews.length+1)].map(() => new Array(delta.length+1).fill(0));
        for (let i=1; i<=subviews.length; i++) { // Start with an m x n table of zeroes where m is the length of the new iterable and n is the old.
            for (let j=1; j<=delta.length; j++) { // Walk all cells and, if the templates match at i,j advance each counter and the length of the longest subsequence.
                if (equals(subviews[i-1].key(), delta[j-1].key())) { //TODO expand view fns before testing equality, preferably at the start so everything is expanded always
                    lcs[i][j] = lcs[i-1][j-1] + 1; }
                else { // Otherwise, preserve the maximum subsequence length coming from advancing either index to this step.
                    lcs[i][j] = Math.max(lcs[i][j-1], lcs[i-1][j]); }}}
        return lcs; }

    diffDOM (lcs, subviews, delta, sub, model) { // Decode the length table and perform swaps/insertions/deletions
        let i = lcs.length - 1, j = lcs[0].length - 1;

        while (i || j) { // Go all the way to 0 to ensure all insertions/deletions.
            if (i && j && equals(subviews[i-1].key(), delta[j-1].key())) { // If we can reuse a template,
                log('rerender', this.constructor.name, 'swap', subviews[i-1].key(), subviews[i-1], delta[j-1]);
                delta[j-1] = delta[j-1].adoptChild(subviews[i-1], sub, model, this.vvar); // steal the previous child and rerender it.
                i--; j--; }
            
            else if (!i || lcs[i-1][j] <= lcs[i][j-1]) { // If we need to skip a delta, insert it at current position
                //delta[j-1].child = render(delta[j-1].template, sub, model);
                log('rerender', this.constructor.name, 'add', delta[j-1].key(), delta[j-1]);
                delta[j-1] = delta[j-1].rerenderChild(sub, model); //TODO can we reuse model value here if cached in model item
                if (!subviews.length) this.comment.after(delta[j-1].render()); // If no previous subviews, comment must have been added by render
                else if (j === delta.length) { // If we haven't yet added any new deltas, use the last previous subview (if attached).
                    if (subviews[subviews.length-1].lastNode()) subviews[subviews.length-1].lastNode().after(delta[j-1].render());
                }
                else { // Otherwise, insert delta in front of previous delta (which may be a swap from previous subviews).
                    delta[j].firstNode().before(delta[j-1].render());
                }
                j--; }
            
            else { // Skipping a dom node, so remove it
                log('rerender', this.constructor.name, 'delete', subviews[i-1].key(), delta[j-1]?.key(), subviews[i-1]);
                subviews[i-1].remove();
                i--; }}}

    remove() { this.child.remove(); }
    items(a=[]) {
        this.child.items(a);
        return a; }
    firstNode() { return this.child.firstNode(); }
    lastNode() { return this.child.lastNode(); }}

class IterableModelRoot extends IterableViewRoot {
    constructor(model, ...args) {
        super(...args);
        this.model = model; }
    recreate(child) { return new this.constructor(this.model, this.vvar, this.ovar, child, this.comment); }
    rerender(sub, model) { return super.rerender(sub, this.model); }
}

class IterableViewBranch {
    constructor(lhs, rhs, goal) {
        this.goal = goal;
        this.lhs = lhs;
        this.rhs = rhs; }
    remove() {
        this.lhs.remove();
        this.rhs.remove(); }
    toArray(a) {
        this.lhs.toArray(a);
        this.rhs.toArray(a);
        return a; }
    rerender(sub, model, vvar, ovar) {
        var sub = this.goal.apply(sub); //TODO make branches hold their own failure flag for early stopping
        return new IterableViewBranch(this.lhs.rerender(sub, model, vvar, ovar), this.rhs.rerender(sub, model, vvar, ovar), this.goal); }
    items(a=[]) {
        this.lhs.items(a);
        this.rhs.items(a);
        return a; }
    firstNode() { return this.lhs.firstNode(); }
    lastNode() { return this.rhs.lastNode(); }
    asGoal() { return this.goal.conj(this.lhs.asGoal().disj(this.rhs.asGoal())); }}

class IterableFailure { // Failures on the initial render that may expand to leaves or branches.
    constructor(renderer, goal) {
        this.goal = goal;
        this.renderer = renderer; }
    items(a=[]) { return a; }
    rerender(sub, mvar, vvar, ovar) { return this.goal.expand_run(sub, (g, s) => this.renderer.render(g, s, vvar, mvar, ovar)); }}

class IterableFailedItem { // Rerender failures of atomic leaves that may cache nodes
    constructor(child) {
        this.child = child; }
    items(a=[]) { return a; }
    rerender(sub, mvar, vvar, ovar) {
        log('rerender', this.constructor.name, this.child, sub.reify(vvar), sub.reify(mvar));
        return this.child.rerender(sub, mvar, vvar, ovar); }}

class IterableViewItem { // Displayable iterable item
    constructor(goal, template=null, child=null, order=null) {
        this.goal = goal;
        if (template instanceof LVar) throw Error('unbound template: ' + template + ' ' + goal);
        this.child = child;
        this.template = template;
        this.order = order; }
    static create(sub, goal, vvar, mvar, ovar) {
        let tmpl = sub.reify(vvar);
        return new this(goal, tmpl, render(tmpl, sub, mvar), sub.reify(ovar)); }
    recreate(sub, goal, vvar, mvar, ovar) {
        let tmpl = sub.reify(vvar);
        return new this.constructor(this.goal, tmpl, equals(tmpl, this.template) ? this.child : null, sub.reify(ovar)); }
    key() { return this.template; }
    remove() { this.child.remove(); }
    firstNode() { return this.child.firstNode(); }
    lastNode() { return this.child.lastNode(); }
    items(a=[]) {
        a.push(this);
        return a; }
    toArray(a) { a.push(this); return a; }
    render() {
        let n = this.child.render();
        log('render', this.constructor.name, n);
        return n; }
    
    rerender(sub, mvar, vvar, ovar) {
        log('rerender', this.constructor.name, this.goal+'', vvar+'', toString(sub), mvar+'');
        var sub = this.goal.apply(sub);
        if (sub.isFailure()) return new IterableFailedItem(this);
        return this.recreate(sub, this.goal, vvar, mvar, ovar); }

    rerenderChild(sub, mvar) { // TODO consider avoiding mutation in child rerender
        log('rerender', 'child', this.constructor.name, this.template, this.child, toString(sub));
        if (this.child) this.child = this.child.rerender(sub, mvar);
        else this.child = render(this.template, sub, mvar);
        return this; }

    adoptChild(previtem, sub, mvar, vvar) { //TODO try to merge adopt and rerender child
        log('rerender', this.constructor.name, 'adopt', this, previtem);
        this.child = previtem.child.rerender(sub, mvar, vvar);
        delete previtem.child;
        return this; }
    
    static render(goal, sub, vvar, mvar, order) {
        log('parse', this.name, goal+'', toString(sub));
        if (!sub) return new IterableFailure(this, goal);
        return this.create(sub, goal, vvar, mvar, order); }}

class IterableModelItem extends IterableViewItem {
    constructor(model, ...args) {
        super(...args);
        this.model = model; }
    static create(sub, goal, vvar, mvar, ovar) {
        return new this(sub.reify(mvar), goal, vvar, render(vvar, sub, mvar), sub.reify(ovar)); }
    recreate(sub, goal, vvar, mvar, ovar) {
        let model = sub.reify(mvar);
        return new this.constructor(model, this.goal, vvar, model === this.model ? this.child : null, sub.reify(ovar)); }
    key() { return this.model; }
    extend(sub, mvar) { return sub.extend(mvar, this.model); }
    adoptChild(previtem, sub, mvar, vvar) { return super.adoptChild(previtem, this.extend(sub, mvar), mvar, vvar); }
    rerenderChild(sub, mvar) { return super.rerenderChild(this.extend(sub, mvar), mvar); }}

class ViewDOMNode extends View { 
    constructor(properties, children=[], node=null) { //TODO a domnode can prune all non dynamic children at the start since they will never update. may not be necessary if we only need 1 level of matching (and nested levels handled with pure updating), but if it is make sure to check for recursive loops like building <ul>
        super();
        this.properties = properties;
        this.node = node;
        this.children = children; }
    render() {
        log('render', this.constructor.name, this.node?.outerHTML);
        if (this.node) return this.node;
        this.node = document.createElement(this.properties.tagName || 'div');
        for (let k in this.properties) { if (k !== 'tagName') this.node[k] = this.properties[k]; }
        for (let c of this.children) this.node.appendChild(c.render());
        return this.node; }
    rerender(sub, model) {
        return new ViewDOMNode(this.properties, this.children.map(c => c.rerender(sub, model)), this.node);
    }
    remove() { if (this.node) this.node.remove(); }
    firstNode() { return this.node; }
    lastNode() { return this.node; }}

class ViewTextNode extends View {
    constructor(text) {
        super();
        this.text = text;
        this.node = null; }
    render() {
        log('render', this.constructor.name, this.text, this.node); //TODO find out why we have to add to parent & whether that applies to dom node as well
        return this.node = this.node || document.createTextNode(this.text); }
    rerender(sub, model, vvar) { return this; }
    remove() { if (this.node) this.node.remove(); }
    firstNode() { return this.node; }
    lastNode() { return this.node; }}


class Template {
    constructor(template) {
        this.template = template; }
    render(sub, mdl) {
        log('parse', this.constructor.name, this.template, toString(sub))
        return render(this.template, sub, mdl); }
    model(m) { return new ModelTemplate(m, this.template); }
}

class ModelTemplate extends Template {
    constructor(model, ...args) {
        super(...args);
        this.modelf = model; }
    render(sub, mdl) {
        let v = new LVar().name('modelview'), o = new LVar().name('order'), g = to_goal(this.modelf(v, mdl, o));
        log('parse', this.constructor.name, this.template, g, toString(sub))
        let c = g.expand_run(sub, (g, s) => IterableModelItem.render(g, s, this.template, v, o));
        return new IterableModelRoot(v, this.template, o, c); }
}

function view(template) { return new Template(template); }

export {RK, nil, cons, list, List, Pair, LVar, primitive, succeed, fail, fresh, conde, unify, reunify, failure, Goal, quote, QuotedVar, conj, SVar, render, view};
