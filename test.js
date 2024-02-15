let logging = false;
function log() {
    if (logging) console.log(arguments);
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


class LVar {
    constructor(id) {
	this.id = id;
    }
}

class PropObserver {
    constructor(node, attr, val) {
	this.node = node;
	this.attr = attr;
	this.val = val;
    }
}

class List {

}

class Cons extends List {
    constructor(car, cdr) {
	super();
	this.car = car;
	this.cdr = cdr;
    }
}

class Empty extends List {

}

const nil = new Empty();

function normalize(model, substitution) {
    if (model instanceof LVar) {
	return model;
    }
    else if (Array.isArray(model)) {
	let tail = new LVar(substitution.push(nil) - 1);
	for (let i=model.length-1; 0<=i; i--) {
	    tail = new LVar(substitution.push(new Cons(normalize(model[i], substitution), tail)) - 1);
	}
	return tail;
    }
    else if (typeof model == 'object') {
	let m = {};
	for (const k in model) {
	    m[k] = normalize(model[k], substitution);
	}
	return new LVar(substitution.push(m) - 1);
    }
    else {
	return new LVar(substitution.push(model) - 1);
    }
}

function walk(substitution, lvar) {
    if (!(lvar instanceof LVar)) return lvar;
	return substitution[lvar.id];
}


// RENDERING

function render(spec, sub, observers) {
    log('render', spec, sub, observers);
    assert(sub);
    if (typeof spec == 'string' || typeof spec == 'number') return document.createTextNode(spec);
    else if (Array.isArray(spec)) {
	let parent = document.createElement(spec[0]);
	for (let i=1; i<spec.length; i++) {
	    log('child render', render(spec[i], sub, observers));
	    parent.appendChild(render(spec[i], sub, observers));
	}
	return parent;
    }
    else if (spec instanceof LVar) {
	return render(walk(sub, spec), sub, observers);
	
	
    }
    else throw Error('Unrecognized render spec: ' + JSON.stringify(spec));
    //    		typeof child === 'number') head.appendChild(document.createTextNode(child));
    //document.createDocumentFragment());}
}


// TESTING

let s = [];
let m = normalize({
    a: 1,
    b: 2,
    c: [3, 4],
    d: {e: 5, f: 6}
}, s);




log("model",m);
log("substitution",s);

assert(walk(s, m).a instanceof LVar, walk(s, m).a);
asserte(render(walk(s,m).a, s).textContent, '1');
