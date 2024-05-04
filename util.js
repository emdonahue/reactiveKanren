let is_logging = false;

function logging(on, ...channel) {
    is_logging = (typeof on == 'boolean') ? on : [on, ...channel];
}

function log(...args) {
    if (true === is_logging || Array.isArray(logging) && logging.every((e,i) => e === args[i])) console.log.apply(console, args.map(toString));
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
