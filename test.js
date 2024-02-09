
class LVar {
    constructor(id) {
	this.id = id;
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

let subst = [];
let m = normalize({
    a: 1,
    b: 2,
    c: [3, 4]
}, subst);
console.log(subst);
