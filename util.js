let is_logging = false;

function logging(b) {
    is_logging = b;
}

function log(...args) {
    if (is_logging) console.log.apply(console, args.map(toString));
    return args[args.length-1];
}

function dlog(...args) {
    console.log.apply(console, args.map(toString));
    return args[args.length-1];
}

function toString(x) {
    return x.toString && x.toString === Object.prototype.toString ? JSON.stringify(x) : x.toString();
}


function copy(x) {
    return Object.assign(Object.create(Object.getPrototypeOf(x)), x);
}

export {logging, log, dlog, copy, toString}
