let logging_channels = [];

function logging(on, ...channel) {
    if (!on) logging_channels = [];
    else logging_channels.push([on, ...channel]);
}

function log(...args) {
    if (logging_channels.some(ch => ch.every((e,i) => e == args[i]))) {
        console.log.apply(console, args.map(toString));
    }
    return args[args.length-1];
}

function dlog(...args) {
    console.log.apply(console, args.map(toString));
    return args[args.length-1];
}

function toString(x) {
    return !x || (x.toString && x.toString === Object.prototype.toString) ? JSON.stringify(x) : x.toString();
}


function copy(x) {//TODO convert to structuredclone?
    return Object.assign(Object.create(Object.getPrototypeOf(x)), x);
}

function equals(x, y) {
    return (x == y)
        || (Array.isArray(x) && Array.isArray(y) && x.length == y.length && x.every((e,i) => equals(e, y[i])))
        || (Object.prototype.toString.call(x) !== '[object String]' && x.constructor === y.constructor  && Object.keys(x).length === Object.keys(y).length && Object.entries(x).every(([k,v]) => equals(v, y[k])));
}

export {logging, log, dlog, copy, toString, equals}
