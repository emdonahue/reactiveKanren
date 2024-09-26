let logging_channels = [];

function logging(on, ...channel) {
    if (!on) logging_channels = [];
    else logging_channels.push([on, ...channel]);
}

function log(...args) {
    if (logging_channels.some(ch => ch.every((e,i) => e === true || e == args[i]))) {
        console.log.apply(console, args);
    }
    return args[args.length-1];
}

function subToArray(sub) {
    let a = [];
    sub.map(e => a[e.car] = toString(e.cdr));
    return a;
}

function assert(...assertions) {
    let as = [...assertions];
    for (let i in as) if (!as[i]) throw Error('Assertion Failed: ' + i); }

function toString(x) {
    if (x instanceof Node) return x;
    return !x || (x.toString && x.toString === Object.prototype.toString) ? JSON.stringify(x) : x.toString();
}


function copy(x) {//TODO convert to structuredclone?
    if (x instanceof Array) return [...x];
    return Object.assign(Object.create(Object.getPrototypeOf(x)), x);
}

function copy_empty(x) {
    return Array.isArray(x) ? [] : Object.create(Object.getPrototypeOf(x));
}

function equals(x, y) {
    return (x === y)
        || (Array.isArray(x) && Array.isArray(y) && x.length == y.length && x.every((e,i) => equals(e, y[i])))
        || (x && y &&
            !(x instanceof Node) &&
            !is_string(x) &&
            !is_number(x) &&
            !is_boolean(x) &&
            x.constructor === y.constructor  && Object.keys(x).length === Object.keys(y).length && Object.entries(x).every(([k,v]) => equals(v, y[k])));
}

function is_string(x) { return Object.prototype.toString.call(x) === '[object String]'; }
function is_number(x) { return Object.prototype.toString.call(x) === '[object Number]'; }
function is_boolean(x) { return Object.prototype.toString.call(x) === '[object Boolean]'; };
function is_pojo(x) { return !!x && Object.getPrototypeOf(x) === Object.prototype; };


export {logging, log, copy, toString, equals, is_string, is_number, is_boolean, is_pojo, assert, subToArray, copy_empty}
