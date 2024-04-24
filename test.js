let logging = false;
function log(...args) {
    if (logging) console.log.apply(console, args);
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
    if (!equals(a, b)) throw Error(JSON.stringify(a) + ' != ' + JSON.stringify(b));
}

function primitive(x) {
    return typeof x == 'string' || typeof x == 'number' || x instanceof Empty;
}

class LVar {
    static id = 0;
    constructor() {
	this.id = LVar.id++;
    }
    toString() {
        return '<' + this.id + '>';
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
    run(n) {
        return this.eval(new State(nil)).take(n).map(s => s.reify(nil));
        
    }
}

class Succeed extends Goal {
    eval(s) { return s }
}
var succeed = new Succeed;

class Fail extends Goal {
    eval(s) { return failure }
}
var fail = new Fail;

class Conj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    eval(s) {
        return this.lhs.run(s).eval(this.rhs);
    }
}

class Disj extends Goal {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class Fresh extends Goal {
    constructor(vars, ctn) {
        super();
        this.vars = vars;
        this.ctn = ctn;
    }
    run(n) {
        //console.log(this.ctn, this.vars+'', this.ctn(...this.vars).eval(new State(nil)));
        return this.ctn(...this.vars).eval(new State(nil)).take(n).map(s => s.reify(this.vars));        
    }
    eval(s) {
        return new Suspended(s, this.ctn(...this.vars));
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
}

class State extends Stream {
    constructor(sub) {
        super();
        this.substitution = sub;
    }
    take(n) { return List.from(this) }
    reify(x) { return this.substitution.reify(x) }
    unify(x, y) { return new State(this.substitution.unify(x, y)) }
}

class Suspended extends Stream {
    constructor(s, g) {
        super();
        this.state=s;
        this.goal = g;
    }
}

class MPlus extends Stream {
    constructor(lhs, rhs) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class PropObserver {
    constructor(lvar, node, attr) {
        this.lvar = lvar;
	this.node = node;
	this.attr = attr;
    }

    update(val) {
	this.node[this.attr] = val;
        return true;
    }
}

class IterObserver {
    constructor(lvar, node) {
        this.lvar = lvar;
	this.node = node;
    }

    update(val) {
        if (val instanceof Pair) return true;
        this.node.remove();
        return false;
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
        return '(' + this.toArray().join(' ') + ')';
    }
    unify(x, y) {
        x = this.walk(x);
        y = this.walk(y);
        if (x == y) return this;
        if (x instanceof LVar) return this.acons(x, y);
        if (y instanceof LVar) return this.acons(y, x);
        if (x instanceof Pair && y instanceof Pair) return this.unify(x.car, y.car).unify(x.cdr, y.cdr);
        return failure;
    }
    eval(g) {
        return g.eval(this);
    }
}

class Pair extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
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
}

const nil = new Empty();

class Failure {
    unify() { return this };
    reify(x) { return x };
    eval(x) { return this };
}
var failure = new Failure;

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


// RENDERING

function render(spec, sub=nil, obs=nil, model={}) {
    log('render', spec, sub, obs, model);
    if (typeof spec == 'string' || typeof spec == 'number') { // Simple Text nodes
	let node = document.createTextNode(spec);
	//return [node, new PropObserver(node, 'textContent')];
	return [node, sub, obs];
    }
    else if (spec instanceof Function) {
        return render(spec(model), sub, obs, model);
    }
    else if (Array.isArray(spec)) { // Build a DOM node
        let head_spec = sub.walk(spec[0]);
        if (head_spec instanceof List) { // Build an iterable DOM list
            let parent = document.createDocumentFragment();
            let items = head_spec;
            let linkvar = spec[0];
            
            while (items instanceof Pair) { //TODO deal with lvar tailed improper lists
                var [node, sub, obs] = render(spec[1], sub, obs, items.car);
                parent.appendChild(node);
                obs = obs.cons(new IterObserver(linkvar, node));
                linkvar = items.cdr;
                items = sub.walk(linkvar);
            }
            return [parent, sub, obs];
        } // Build a head node for the rest of the child specs
        else if (typeof head_spec == 'string'){
	    let parent = document.createElement(head_spec);
	    for (let i=1; i<spec.length; i++) {
	        log('child render', render(spec[i], sub, obs, model));
                var [node, sub, obs] = render(spec[i], sub, obs, model);
                parent.appendChild(node);
	    }
	    return [parent, sub, obs];
        }
        else throw Error('Unrecognized render spec head: ' + JSON.stringify(head_spec));
    }
    else if (spec instanceof LVar) { // Build a watched Text node
	var [node, sub, obs] = render(sub.walk(spec), sub, obs, model);
	return [node, sub, obs.cons(new PropObserver(spec, node, 'textContent'))];
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
    //    		typeof child === 'number') head.appendChild(document.createTextNode(child));
    //document.createDocumentFragment());}
}

// UPDATING

function update(sub, obs) {
    return obs.filter((o) => o.update(sub.walk(o.lvar)));
}

function garbage_collect(sub, root) {
    return garbage_sweep(sub, garbage_mark(sub, root));
}

function garbage_mark(sub, root, marked=nil) {
    // Return vars in sub still reachable from root.
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


let [m, s] = normalize({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, nil);

log("model",m);
log("substitution",s);

//Model
assert(s.walk(m).a instanceof LVar, s.walk(m).a);
asserte(garbage_mark(s, m).length(), 17);
asserte(garbage_mark(s.acons(s.walk_path(m, 'c'), s.walk_path(m,'a')), m).length(), 12);
asserte(garbage_sweep(s, garbage_mark(s.acons(s.walk_path(m, 'c'), s.walk_path(m,'a')), m)).length(), 12);

//Template
asserte(render(s.walk(m).a, s, nil, m)[0].textContent, '1');

//DOM

var o = nil; // observers: convert substitution values into dom updates

// Static
asserte(render('lorem', s, o, m)[0].textContent, 'lorem'); // Static text node
asserte(render(['div', 'lorem'], s, o, m)[0].innerHTML, 'lorem'); // Static dom node
asserte(render(['div', ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem'); // Static nested dom node

// Dynamic
var [n,,o] = render(s.walk(m).a, s, o, m);
asserte(n.textContent, '1');
update(s.acons(s.walk(m).a, 2), o);
asserte(n.textContent, '2');

// Lists
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', 'lorem']], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return 'lorem' }]], s, o, m)[0].childNodes[0].innerHTML, 'lorem');
asserte(render([List.fromArray(['ipsum', 'dolor']), ['div', function (e) { return e }]], s, o, m)[0].childNodes[0].innerHTML, 'ipsum');


var [todo_model, todo_sub] =
    normalize({todos: [{title: 'get todos displaying', done: false},
                       {title: 'streamline api', done: false}]});

//console.log(todo_sub + '')
var [todo_node, todo_sub, todo_obs] =
    render(['div',
            [todo_sub.walk(todo_model).todos,
             ['div', function (e) {return todo_sub.walk_path(e, 'title')}]]],
           todo_sub, nil, todo_model);
asserte(todo_node.childNodes.length, 2);
/*
console.log(todo_sub + '')
console.log(todo_sub.reify() + '')
console.log(todo_obs.map((x) => x.lvar) + '')
console.log(todo_sub.walk_path(todo_model, 'todos', 'cdr'))
console.log(todo_sub.walk_path(todo_model, 'todos', 'cdr', 'cdr'))
console.log(garbage_collect(
    todo_sub.acons(todo_sub.walk_path(todo_model, 'todos', 'cdr'),
                   todo_sub.walk_path(todo_model, 'todos', 'cdr', 'cdr')), todo_model) + '');
*/
//console.log(todo_sub.reify(todo_sub.walk(todo_model).todos) + '')
//console.log(todo_sub.acons(todo_sub.walk_path(todo_model, 'todos', 'cdr'),
//                           todo_sub.walk(todo_sub.walk_path(todo_model, 'todos', 'cdr', 'cdr'))) + '');
todo_sub = garbage_collect(
    todo_sub.acons(todo_sub.walk_path(todo_model, 'todos', 'cdr'),
                   todo_sub.walk_path(todo_model, 'todos', 'cdr', 'cdr')), todo_model)
//console.log(todo_sub + '')
todo_obs = update(todo_sub, todo_obs);
asserte(todo_node.childNodes.length, 1);


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
//console.log(todo_sub)


// MK TEST

asserte((new Succeed).run(), List.from(nil));
asserte(fresh((x) => x.unify(1)).run(), List.from(List.from(1)));

//asserte(fresh((x, y) => x.unify(1).conj(y.unify(2))).run(), List.from(1, 2));

document.body.appendChild(todo_node);

console.log('Tests Complete');
