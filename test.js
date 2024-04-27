//TODO make set unify always pick the non temporary variable to set. maybe insert special perma vars with normalize

let logging = false;
function log(...args) {
    if (logging) console.log.apply(console, args.map(toString));
    return args.length == 1 ? args[0] : args;
}

function dlog(...args) {
    console.log.apply(console, args.map(toString));
    return args.length == 1 ? args[0] : args;
}

function test(f, test_name) {
    try {
	f();
    } catch (x) {
	document.write('error in test: ' + (test_name || 'Unnamed'));
	throw x;
    }
}

function assert(a, ...debug_info) {
    if (!a) {
	console.log(...debug_info);
	throw Error("Assertion failed");
    }
}

function equals(a, b) {
    return JSON.stringify(a) == JSON.stringify(b);
}

function asserte(a, b) {
    if (!equals(a, b)) throw Error(toString(a) + ' != ' + toString(b));
}

function toString(x) {
    return x.toString && x.toString === Object.prototype.toString ? JSON.stringify(x) : x.toString();
}

function primitive(x) {
    return typeof x == 'string' || typeof x == 'boolean' || typeof x == 'number' || x instanceof Empty || x === null || x === undefined;
}

function copy(x) {
    return Object.assign(Object.create(Object.getPrototypeOf(x)), x);
}

class LVar {
    static id = 0;
    constructor() {
	this.id = LVar.id++;
        this.label = '';
    }
    toString() {
        return '<' + this.label + this.id + '>';
    }
    unify(x) {
        return new Unify(this, x);
    }
}

class Goal {
    conj(x) {
        return new Conj(this, x);
    }
    disj(x) {
        return new Disj(this, x);
    }
    run(n=1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => s.update_substitution()).map(s => reify ? s.reify(nil) : s);
        
    }
    suspend(s) { return new Suspended(s, this) }
}

class Succeed extends Goal {
    eval(s) { return s }
    suspend(s) { return s }
}
var succeed = new Succeed;

class Fail extends Goal {
    eval(s) { return failure }
    suspend(s) { return failure }
}
var fail = new Fail;

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return this.rhs.eval(this.lhs.eval(s));
    }
}

class Disj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return this.lhs.eval(s).mplus(this.rhs.eval(s));
    }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n=1, {reify=true, substitution=nil}={}) {
        return this.eval(new State(substitution)).take(n).map(s => s.update_substitution()).map(s => reify ? s.reify(this.vars) : s);
    }
    eval(s) {
        return to_goal(this.ctn(...this.vars)).suspend(s);
    }
}

class Unify extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return s.unify(this.lhs, this.rhs);
    }
}

class Stream {
    mplus(s) { return s._mplus(this) }
    _mplus(s) { return new MPlus(this, s) }
    take(n) {
        let s = this;
        while (s.isIncomplete()) { s = s.step() }
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
var failure = new Failure;

class State extends Stream {
    constructor(sub=nil, updates=nil) {
        super();
        this.substitution = sub;
        this.updates = updates;
    }
    take(n) { return List.from(this) }
    reify(x) { return this.substitution.reify(x) }
    unify(x, y) {
        let s = this.substitution.unify(x, y);
        if (s == failure) return s;
        return new State(s, this.updates) }
    update(x, y) {
        let s = this.updates.unify(x, y);
        if (s == failure) return s;
        return new State(this.substitution, s) }
    eval(g) { return g.eval(this) }
    isIncomplete() { return false }
    answer() { return this }
    step() { return failure }
    mplus(s) { return new Answers(this, s) }
    _mplus(s) { return new Answers(this, s) }
    update_substitution() {
        log('update_substitution', this.substitution, this.updates);
        s = new State(this.updates.update_substitution(this.substitution));
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
    step() { return this.goal.eval(this.state) }
}

class Answers extends Stream {
    constructor(state, stream) {
        super();
        this.state = state;
        this.stream = stream;
    }
    isIncomplete() { return false }
    answer() { return this.state }
    step() { return this.stream }
    mplus(s) { return new Answers(this.state, this.stream.mplus(s)) }
    _mplus(s) { return new Answers(this.state, this.stream.mplus(s)) }
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

class UnifyUpdate extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) { return s.update(this.lhs, this.rhs) }
}

function to_goal(g) {
    if (Array.isArray(g)) return g.reduceRight((cs, c) => to_goal(c).conj(cs));
    else if (true === g) return succeed;
    else if (false === g) return fail;
    else return g;
}

function conde(...condes) {
    return condes.reduceRight((cs, c) => to_goal(c).disj(cs));
}

function unify(x, y) {
    return new Unify(x, y);
}

function setunify(x, y) {
    return new UnifyUpdate(x, y);
}






// RRP
class PropObserver {
    constructor(lvar, node, attr) {
        this.lvar = lvar;
	this.node = node;
	this.attr = attr;
    }

    update(sub) {
	this.node[this.attr] = sub.walk(this.lvar);
        return true;
    }
}

class IterObserver {
    constructor(lvar, node, lvar_nodes) {
        dlog('iter observer', lvar_nodes)
        this.lvar = lvar;
        this.node = node;
        this.lvar_nodes = lvar_nodes;
    }

    update(sub) {
        // get list of vars still in store
        // remove nodes for all variables no longer in store
        // for all vars in store,
        let ns = this.moddom(this.lvar, sub);
        dlog('ns', ns, this.lvar_nodes)
        dlog('sub', sub)
        this.lvar_nodes = this.lvar_nodes.filter(b => {
            if (ns.member(b.car)) return true;
            dlog('removing', b.car)
            b.cdr.remove();
            return false;
        });
        dlog('lvar nodes', this.lvar_nodes);
                    /*
        this.lvar_nodes = this.lvar_nodes.filter(
            function ({car:v, cdr:n}) {
                dlog('walk', v, sub.walk(v))
                if (!(sub.walk(v) instanceof Pair)) {
                    console.log('remove', sub.walk(v))
                    n.remove();
                    return false; }
                return true;
            });
*/
        //if (val instanceof Pair) return true;
        //this.node.remove();
        //return false;
        return true;
    }
    moddom(lvar, sub) {
        let w = sub.walk(lvar);
        if (w instanceof Empty) {
            return nil;
        }
        assert(w instanceof Pair);
        return this.moddom(w.cdr, sub).cons(lvar);
    }
    
}

class List {
    static fromArray(a) {
        let l = nil;
        for (const e of a.reverse()) {
            l = l.cons(e);
        }
        return l;
    }
    static fromTree(a) {
        return this.fromArray(a).map(x => Array.isArray(x) ? this.fromTree(x) : x);
    }
    static from(...e) {
        return this.fromArray([...e]);
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
        if (x == y) return this;
        if (x instanceof LVar) return this.acons(x, y_var);
        if (y instanceof LVar) return this.acons(y, x_var);
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
    caar() { return this.car.car }
    cdar() { return this.car.cdr }
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
    update_substitution(s) { // Called on the updates substitution with the normal substitution as a parameter.
        //console.log('sub',s+'',this+'',s.update_binding(this.caar(), this.cdar())+'', this.cdr.update_substitution(s.update_binding(this.caar(), this.cdar()))+'')
        return this.cdr.update_substitution(s.update_binding(this.caar(), this.cdar()));
    }
    update_binding(x, y) {
        log('update_binding', x, y, this);
        let b = this.walk_binding(x);
        if (primitive(y) || y instanceof LVar) return this.acons(b.car, y);
        let val = b.cdr;
        if (primitive(val)) {
            let [n, s] = normalize(y, this);
            return s.acons(b.car, n); // may be able to walk n and store the reified structure directly, simplifying primitive storage
        }
        let s = this;
        let u = copy(y);
        //console.log(x,y,b);
        for (let k in u) {
            if (Object.hasOwn(val, k)) {
                s = s.update_binding(val[k], y[k]);
                u[k] = val[k];
            }
            else {
                let n;
                [n, s] = normalize(u[k], this);
                u[k] = n;
            }
        }
        return s.acons(b.car, u);
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
    memp(p) { return undefined };
    filter(p) { return this };
    map(f) { return this };
    update_substitution(s) { return s }
    update_binding(x, y) { return this.acons(x, y) }
    _toString() { return '' }
}

const nil = new Empty();

// MK

function fresh(f) {
    return new Fresh(List.repeat(f.length, () => new LVar()), f);
}


// RRP

function normalize(model, substitution=nil) {
    log('normalize', model, substitution);
    if (model instanceof LVar) {
	return [model, substitution];
    }
    else if (Array.isArray(model)) {
	let tail = new LVar();
        substitution = substitution.acons(tail, nil);
	for (let i=model.length-1; 0<=i; i--) {            
            var [lvar, substitution] = normalize(model[i], substitution);
	    let tail2 = new LVar();
            substitution = substitution.acons(tail2, new Pair(lvar, tail));
            tail = tail2;
	}
	return [tail, substitution];
    }
    else if (typeof model == 'object') {
	let m = {};
	for (const k in model) {
	    //log('k',k,'submodel',model[k], 'substitution',JSON.stringify(substitution));
            var [lvar, substitution] = normalize(model[k], substitution);
            const lvar2 = new LVar();
            substitution = substitution.acons(lvar2, lvar);
	    m[k] = lvar2;
            //substitution = substitution.push(new LVar(substitution.push(lvar) - 1)) - 1
	    //log('id',m[k],'substitution',JSON.stringify(substitution));
	}
        const mvar = new LVar();
	return [mvar, substitution.acons(mvar, m)];
    }
    else {
        const lvar = new LVar();
	return [lvar, substitution.acons(lvar, model)];
    }
}

function normalize2(model, sub=nil) {
    if (primitive(model) || model instanceof LVar) return [model, sub];
    else if (Array.isArray(model)) { return normalize2(List.fromArray(model), sub); }
    else {
        let m = Object.create(Object.getPrototypeOf(model));
        let n;
        for (let k in model) {
            assert(!(model[k] instanceof LVar)); //normalized values should be fully ground
            let v = new LVar();
            [n,sub] = normalize2(model[k], sub);
            sub = sub.acons(v, n);
            m[k] = v;
        }
        return [m, sub];
    }
}

// RENDERING

function render(spec, sub=nil, obs=nil, model={}, update=()=>{}) {
    log('render', spec, sub, obs, model);
    if (typeof spec == 'string' || typeof spec == 'number') { // Simple Text nodes
	let node = document.createTextNode(spec);
	//return [node, new PropObserver(node, 'textContent')];
	return [node, sub, obs];
    }
    else if (spec instanceof Function) {
        return render(spec(model), sub, obs, model, update);
    }
    else if (Array.isArray(spec)) { // Build a DOM node
        let head_spec = sub.walk(spec[0]);
        if (head_spec instanceof List) { // Build an iterable DOM list
            let parent = document.createDocumentFragment();
            let items = head_spec;
            let linkvar = spec[0];
            let listvar = spec[0]; //TODO in simple static list cases this may not be a var
            let listnode = document.createComment('');
            let vars_nodes = [];
            
            while (items instanceof Pair) { //TODO deal with lvar tailed improper lists
                var [node, sub, obs] = render(spec[1], sub, obs, items.car, update);
                parent.appendChild(node);
                vars_nodes.push(new Pair(linkvar, node));
                //obs = obs.cons(new IterObserver(linkvar, node));
                linkvar = items.cdr;
                items = sub.walk(linkvar);
            }
            return [parent.appendChild(listnode) && parent, sub, obs.cons(new IterObserver(listvar, listnode, List.fromArray(vars_nodes)))];
        } // Build a head node for the rest of the child specs
        else if (typeof head_spec == 'string'){
	    return render([{tagName:head_spec}].concat(spec.slice(1)), sub, obs, model, update);
        }
        else if (head_spec.prototype === undefined) {
            let parent = document.createElement(head_spec.tagName || 'div');
            for (let k in head_spec) {
                if (k === 'tagName') continue;
                if (k.substring(0,2) == 'on') {
                    (k => {
                        parent.addEventListener(
                            k.substring(2),
                            function(e) {
                                update(head_spec[k](model, e));
                            }
                        );})(k);
                }
                else parent[k] = head_spec[k];
            }
	    for (let i=1; i<spec.length; i++) {
	        log('child render', render(spec[i], sub, obs, model, update));
                var [node, sub, obs] = render(spec[i], sub, obs, model, update);
                parent.appendChild(node);
	    }
	    return [parent, sub, obs];
        }
        else throw Error('Unrecognized render spec head: ' + JSON.stringify(head_spec));
    }
    else if (spec instanceof LVar) { // Build a watched Text node
	var [node, sub, obs] = render(sub.walk(spec), sub, obs, model, update);
	return [node, sub, obs.cons(new PropObserver(spec, node, 'textContent'))];
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
    //    		typeof child === 'number') head.appendChild(document.createTextNode(child));
    //document.createDocumentFragment());}
}

// UPDATING

function update(sub, obs) {
    return obs.filter((o) => o.update(sub));
}

function garbage_collect(sub, root) {
    return garbage_sweep(sub, garbage_mark(sub, root));
}

function garbage_mark(sub, root, marked=nil) {
    // Return vars in sub still reachable from root.
    log('garbage_mark', root, marked);
    if (root instanceof LVar) {
        if (marked.member(root)) return marked;
        return garbage_mark(sub, sub.assoc(root), marked.cons(root));
    }
    else if (primitive(root)) {
        return marked;
    }
    else {
        for (const p in root) {
            marked = garbage_mark(sub, root[p], marked);
        }
        return marked;
    }
}

function garbage_sweep(sub, marked) {
    return sub.filter((b) => marked.member(b.car));
}

// TESTING

logging=false;


let [m, s] = normalize2({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, nil);

log("model",m);
log("substitution",s);

//Model
assert(s.walk(m).a instanceof LVar, s.walk(m).a);
asserte(garbage_mark(s, m).length(), 10);
asserte(garbage_mark(s.acons(m.c, m.a), m).length(), 6);
asserte(garbage_sweep(s, garbage_mark(s.acons(m.c, m.a), m)).length(), 6);

//Template
asserte(render(s.walk(m).a, s, nil, m)[0].textContent, '1');

//DOM

var o = nil; // observers: convert substitution values into dom updates

// Static
asserte(render('lorem', s, o, m)[0].textContent, 'lorem');
asserte(render(['div', 'lorem'], s, o, m)[0].innerHTML, 'lorem');
asserte(render([{tagName: 'div'}], s, o, m)[0].tagName, 'DIV');
asserte(render([{tagName: 'div', name: 'lorem'}], s, o, m)[0].name, 'lorem');
asserte(render(['div', ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');

// Dynamic
var [n,,o] = render(s.walk(m).a, s, o, m);
asserte(n.textContent, '1');
update(s.acons(s.walk(m).a, 2), o);
asserte(n.textContent, '2');

// Lists
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return 'lorem' }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return e }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');

// TDList
var [td_model, td_sub] =
    normalize2({todos: [{title: 'get tds displaying', done: false},
                        {title: 'streamline api', done: false}]});


var [td_node, td_sub, td_obs] =
    render(['div',
            [td_sub.walk(td_model).todos,
             [{onclick: m => {console.log('click model', m); return fresh(x => [unify({title: x}, m), setunify(x, 'event handler works')])}},
              function (e) {return td_sub.walk_path(e, 'title')}]]],
           td_sub, nil, td_model, g => {console.log(g.run(1, {reify:false, substitution: td_sub}).car.substitution + '')
                                        td_sub = g.run(1, {reify:false,
                                                           substitution: td_sub}).car.substitution;
                                        td_obs = update(td_sub, td_obs)});
asserte(td_node.childNodes.length, 3);

console.log(td_sub.reify(td_model))
dlog('pre set', td_sub)
td_sub = fresh((x1, x2, x3) => [unify(td_model,{todos: x1}),
                                unify(x1, new Pair(x2, x3)),
                                setunify(x1, x3)]).run(1, {reify:false,
                                                           substitution: td_sub}).car.substitution;
dlog('delete data', td_sub, td_model)
dlog('garbage mark', garbage_mark(td_sub, td_model))
td_sub = garbage_collect(td_sub, td_model);
dlog('garbage collected', td_sub)
td_obs = update(td_sub, td_obs)
dlog(td_sub)
console.log(td_sub.reify(td_model))


//console.log(td_sub.reify(td_model));
/*
console.log(td_model)
console.log(fresh((td1) => [unify({todos: new Pair({title: td1}, new LVar())}, td_model), setunify(td1, 'updated')]).run(1, {reify: false, substitution: td_sub}).car.substitution + '' );
console.log(fresh((td1) => [unify({todos: new Pair({title: td1}, new LVar())}, td_model), setunify(td1, 'updated')]).run(1, {reify: false, substitution: td_sub}).car.substitution.reify(td_model));

td_sub = fresh((td1) => [unify({todos: new Pair({title: td1}, new LVar())}, td_model),
                         setunify(td1, 'set unify working')]).run(1, {reify: false, substitution: td_sub}).car.substitution
td_obs = update(td_sub, td_obs);

asserte(td_node.childNodes[0].innerHTML, 'set unify working');

td_sub = fresh((x1, x2) => [unify({todos: new Pair(new LVar(), x1)}, td_model),
                            unify(x1, new Pair(new LVar(), x2)),
                            setunify(x1, x2)]).run(1, {reify: false, substitution: td_sub}).car.substitution
td_sub = garbage_collect(td_sub, td_model);

td_obs = update(td_sub, td_obs);
asserte(td_node.childNodes.length, 1);
*/
document.body.appendChild(td_node);



//0: (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//tail deletion
//0: (cons #1 #2)
//1: 'test
//2: #4            (cons #3 #4)
//3 'test2
//4 nil

//head deletion
//0: #2              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//multi deletion
//0: #4              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//multi deletion
//0: #4              (cons #1 #2)
//1: 'test
//2: (cons #3 #4)
//3 'test2
//4 nil

//insertion
//0: (cons #1 #2)
//1: 'test
//2: (cons #6 #7)          #3
//3: (cons #4 #5)
//4 'test2
//5 nil
//6 'test3
//7 #3

//first garbage collect all unreachable items
//if a list observer is changed to something other than original object, particularly a free var, delete its node
//console.log(td_sub)



// MK TEST

asserte(succeed.run(), List.from(nil));
asserte(fresh((x) => unify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x, y) => [x.unify(1), y.unify(2)]).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => [x.unify(1), x.unify(2)]).run(), nil);
asserte(fresh((x, y) => unify(new Pair(x,y), new Pair(1,2))).run(), List.fromTree([[1, 2]]));
asserte(fresh((x, y) => unify({a:x, b:y}, {a:1, b:2})).run(), List.fromTree([[1, 2]]));
asserte(fresh((x) => unify({a:1, b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({b:x}, {a:1, b:2})).run(), List.fromTree([[2]]));
asserte(fresh((x) => unify({a:1, b:2}, {b:x})).run(), List.fromTree([[2]]));
asserte(fresh((x) => conde(x.unify(1), x.unify(2))).run(2), List.fromTree([[1], [2]]));
asserte(fresh((x,y) => [unify(x,new Pair(1, y)), unify(y,new Pair(2, nil))]).run(), List.fromTree([[List.from(1, 2), List.from(2)]]));

//console.log('test',fresh((x) => setunify(x, 1)).run(1,false).car);
asserte(fresh((x) => setunify(x, 1)).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,2), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x) => [unify(x,new Pair(1,2)), setunify(x, 1)]).run(), List.fromTree([[1]]));
asserte(fresh((x,y,z) => [unify(x,new Pair(y,z)), setunify(x, new Pair(1,2))]).run(), List.fromTree([[new Pair(1, 2), 1, 2]]));
asserte(fresh((x) => [unify(x,1), setunify(x, new Pair(1,2))]).run(), List.fromTree([[new Pair(1, 2)]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1, 3]]));
asserte(fresh((x,y) => [unify(x,{a:y}), unify(y,1), setunify(x, {a:1,b:3})]).run(), List.fromTree([[{a:1,b:3}, 1]]));
asserte(fresh((x,y,z) => [unify(x,{a:y,b:z}), unify(y,1), unify(z,2), setunify(x, {b:3})]).run(), List.fromTree([[{b:3}, 1, 3]]));
asserte(fresh((w,x,y,z) => {w.label = 'w'; x.label = 'x'; y.label='y'; z.label='z'; return [unify(x,new Pair(1, y)), unify(y,new Pair(2, nil)), unify(x,w),unify(x,new Pair(1, z)), setunify(x, z)]}).run(), List.fromTree([[new Pair(2, nil), new Pair(2, nil), new Pair(2, nil), new Pair(2, nil)]]));



console.log('Tests Complete');
