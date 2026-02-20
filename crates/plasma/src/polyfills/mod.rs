/// JavaScript polyfill source strings for Node.js API compatibility.
///
/// Each function returns a JS string that, when evaluated by boa, defines
/// a global object or class. These are evaluated during plasma context
/// initialization so they're available before user code runs.

/// Defines `globalThis.process` with env, version, platform, etc.
pub fn process() -> &'static str {
    r#"
(function() {
    globalThis.process = {
        env: {},
        version: "v20.0.0",
        versions: { node: "20.0.0" },
        platform: "wasm",
        arch: "wasm32",
        argv: [],
        cwd: function() { return "/"; },
        nextTick: function(fn) { fn(); },
        stdout: { write: function(s) { console.log(s); } },
        stderr: { write: function(s) { console.log(s); } },
        exit: function(code) { throw new Error("process.exit(" + code + ")"); },
        on: function() { return globalThis.process; },
        once: function() { return globalThis.process; },
        off: function() { return globalThis.process; },
        removeListener: function() { return globalThis.process; },
        emit: function() { return false; },
    };
})();
"#
}

/// Defines `globalThis.EventEmitter` constructor with on/off/emit/once.
pub fn event_emitter() -> &'static str {
    r#"
(function() {
    function EventEmitter() {
        this._events = {};
        this._maxListeners = 10;
    }

    EventEmitter.prototype.on = function(event, fn) {
        if (!this._events[event]) this._events[event] = [];
        this._events[event].push(fn);
        return this;
    };

    EventEmitter.prototype.addListener = EventEmitter.prototype.on;

    EventEmitter.prototype.once = function(event, fn) {
        var self = this;
        function wrapper() {
            self.removeListener(event, wrapper);
            fn.apply(this, arguments);
        }
        wrapper._original = fn;
        return this.on(event, wrapper);
    };

    EventEmitter.prototype.off = function(event, fn) {
        return this.removeListener(event, fn);
    };

    EventEmitter.prototype.removeListener = function(event, fn) {
        if (!this._events[event]) return this;
        this._events[event] = this._events[event].filter(function(listener) {
            return listener !== fn && listener._original !== fn;
        });
        return this;
    };

    EventEmitter.prototype.removeAllListeners = function(event) {
        if (event) { delete this._events[event]; }
        else { this._events = {}; }
        return this;
    };

    EventEmitter.prototype.emit = function(event) {
        if (!this._events[event]) return false;
        var args = Array.prototype.slice.call(arguments, 1);
        var listeners = this._events[event].slice();
        for (var i = 0; i < listeners.length; i++) {
            listeners[i].apply(this, args);
        }
        return true;
    };

    EventEmitter.prototype.listeners = function(event) {
        return this._events[event] ? this._events[event].slice() : [];
    };

    EventEmitter.prototype.listenerCount = function(event) {
        return this._events[event] ? this._events[event].length : 0;
    };

    EventEmitter.prototype.setMaxListeners = function(n) {
        this._maxListeners = n;
        return this;
    };

    EventEmitter.prototype.rawListeners = function(event) {
        return this.listeners(event);
    };

    EventEmitter.prototype.prependListener = EventEmitter.prototype.on;
    EventEmitter.prototype.prependOnceListener = EventEmitter.prototype.once;
    EventEmitter.prototype.eventNames = function() {
        return Object.keys(this._events);
    };

    globalThis.EventEmitter = EventEmitter;
})();
"#
}

/// Defines timer globals: setTimeout, setInterval, clearTimeout, etc.
///
/// Returns timer handle objects with `.ref()`, `.unref()`, and
/// `.hasRef()` methods to match Node.js timer behavior.
pub fn timers() -> &'static str {
    r#"
(function() {
    var _nextId = 1;
    function TimerHandle(id) {
        this._id = id;
        this._ref = true;
    }
    TimerHandle.prototype.ref = function() { this._ref = true; return this; };
    TimerHandle.prototype.unref = function() { this._ref = false; return this; };
    TimerHandle.prototype.hasRef = function() { return this._ref; };
    TimerHandle.prototype[Symbol.toPrimitive] = function() { return this._id; };

    globalThis.setTimeout = function(fn, delay) { return new TimerHandle(_nextId++); };
    globalThis.clearTimeout = function(id) {};
    globalThis.setInterval = function(fn, delay) { return new TimerHandle(_nextId++); };
    globalThis.clearInterval = function(id) {};
    globalThis.setImmediate = function(fn) { return new TimerHandle(_nextId++); };
    globalThis.clearImmediate = function(id) {};
    globalThis.queueMicrotask = function(fn) {};
})();
"#
}

/// Defines `globalThis.TextEncoder` and `globalThis.TextDecoder`.
pub fn text_codec() -> &'static str {
    r#"
(function() {
    globalThis.TextEncoder = function() { this.encoding = "utf-8"; };
    globalThis.TextEncoder.prototype.encode = function(str) {
        var arr = new Uint8Array(str.length);
        for (var i = 0; i < str.length; i++) arr[i] = str.charCodeAt(i) & 0xFF;
        return arr;
    };
    globalThis.TextDecoder = function(enc) { this.encoding = enc || "utf-8"; };
    globalThis.TextDecoder.prototype.decode = function(buf) {
        if (!buf) return "";
        var arr = new Uint8Array(buf.buffer || buf);
        var str = "";
        for (var i = 0; i < arr.length; i++) str += String.fromCharCode(arr[i]);
        return str;
    };
})();
"#
}

/// Defines `globalThis.Buffer` backed by Uint8Array.
pub fn buffer() -> &'static str {
    r#"
(function() {
    function Buffer(arg) {
        if (typeof arg === "number") {
            this._data = new Uint8Array(arg);
        } else if (arg instanceof Uint8Array) {
            this._data = arg;
        } else if (typeof arg === "string") {
            this._data = new Uint8Array(arg.length);
            for (var i = 0; i < arg.length; i++) this._data[i] = arg.charCodeAt(i) & 0xFF;
        } else {
            this._data = new Uint8Array(0);
        }
        this.length = this._data.length;
    }

    Buffer.from = function(data, encoding) {
        if (data instanceof Buffer) return data;
        if (typeof data === "string") return new Buffer(data);
        if (data instanceof Uint8Array) return new Buffer(data);
        if (Array.isArray(data)) return new Buffer(new Uint8Array(data));
        return new Buffer(0);
    };
    Buffer.alloc = function(size) { return new Buffer(size); };
    Buffer.isBuffer = function(obj) { return obj instanceof Buffer; };
    Buffer.byteLength = function(str) {
        if (typeof str === "string") return str.length;
        if (str && str.length !== undefined) return str.length;
        return 0;
    };
    Buffer.concat = function(list, totalLength) {
        if (list.length === 0) return Buffer.alloc(0);
        var total = totalLength || 0;
        if (!totalLength) {
            for (var i = 0; i < list.length; i++) total += list[i].length;
        }
        var result = Buffer.alloc(total);
        var offset = 0;
        for (var i = 0; i < list.length; i++) {
            var src = list[i]._data || list[i];
            for (var j = 0; j < src.length && offset < total; j++) {
                result._data[offset++] = src[j];
            }
        }
        return result;
    };
    Buffer.prototype.toString = function(encoding) {
        var str = "";
        for (var i = 0; i < this._data.length; i++) str += String.fromCharCode(this._data[i]);
        return str;
    };
    Buffer.prototype.slice = function(start, end) { return new Buffer(this._data.slice(start, end)); };
    Buffer.prototype.copy = function(target, tStart, sStart, sEnd) {
        tStart = tStart || 0; sStart = sStart || 0; sEnd = sEnd || this.length;
        for (var i = sStart; i < sEnd; i++) target._data[tStart + (i - sStart)] = this._data[i];
        return sEnd - sStart;
    };
    Buffer.prototype.readUInt8 = function(offset) { return this._data[offset]; };
    Buffer.prototype.writeUInt8 = function(value, offset) {
        this._data[offset] = value & 0xFF;
        return offset + 1;
    };

    globalThis.Buffer = Buffer;
})();
"#
}

/// Defines `globalThis.URL` and `globalThis.URLSearchParams`.
pub fn url() -> &'static str {
    r#"
(function() {
    function URLSearchParams(init) {
        this._params = [];
        if (typeof init === "string") {
            var str = init.charAt(0) === "?" ? init.slice(1) : init;
            if (str) {
                var pairs = str.split("&");
                for (var i = 0; i < pairs.length; i++) {
                    var idx = pairs[i].indexOf("=");
                    if (idx > -1) {
                        this._params.push([
                            decodeURIComponent(pairs[i].slice(0, idx)),
                            decodeURIComponent(pairs[i].slice(idx + 1))
                        ]);
                    } else {
                        this._params.push([decodeURIComponent(pairs[i]), ""]);
                    }
                }
            }
        }
    }
    URLSearchParams.prototype.get = function(name) {
        for (var i = 0; i < this._params.length; i++) {
            if (this._params[i][0] === name) return this._params[i][1];
        }
        return null;
    };
    URLSearchParams.prototype.set = function(name, value) {
        var found = false;
        for (var i = 0; i < this._params.length; i++) {
            if (this._params[i][0] === name) {
                if (!found) { this._params[i][1] = String(value); found = true; }
                else { this._params.splice(i, 1); i--; }
            }
        }
        if (!found) this._params.push([name, String(value)]);
    };
    URLSearchParams.prototype.has = function(name) { return this.get(name) !== null; };
    URLSearchParams.prototype.delete = function(name) {
        this._params = this._params.filter(function(p) { return p[0] !== name; });
    };
    URLSearchParams.prototype.append = function(name, value) {
        this._params.push([name, String(value)]);
    };
    URLSearchParams.prototype.toString = function() {
        return this._params.map(function(p) {
            return encodeURIComponent(p[0]) + "=" + encodeURIComponent(p[1]);
        }).join("&");
    };
    URLSearchParams.prototype.entries = function() { return this._params.slice(); };

    globalThis.URLSearchParams = URLSearchParams;

    function URL(url, base) {
        if (base && typeof url === "string" && url.indexOf("://") === -1) {
            url = base.replace(/\/$/, "") + "/" + url.replace(/^\//, "");
        }
        this.href = url;
        var match = url.match(/^(\w+):\/\/([^/:]+)(:\d+)?(\/[^?#]*)?(\?[^#]*)?(#.*)?$/);
        if (match) {
            this.protocol = match[1] + ":";
            this.hostname = match[2];
            this.port = match[3] ? match[3].slice(1) : "";
            this.pathname = match[4] || "/";
            this.search = match[5] || "";
            this.hash = match[6] || "";
            this.host = this.hostname + (this.port ? ":" + this.port : "");
            this.origin = this.protocol + "//" + this.host;
        } else {
            this.protocol = ""; this.hostname = ""; this.port = "";
            this.pathname = url; this.search = ""; this.hash = "";
            this.host = ""; this.origin = "";
        }
        this.searchParams = new globalThis.URLSearchParams(this.search);
    }
    URL.prototype.toString = function() { return this.href; };

    globalThis.URL = URL;
})();
"#
}

/// Defines legacy `escape()` and `unescape()` globals.
///
/// These are deprecated but still used by some libraries (e.g. discord.js
/// depends on code that calls `escape()`). Boa doesn't provide them by
/// default.
pub fn legacy() -> &'static str {
    r#"
(function() {
    if (typeof globalThis.FinalizationRegistry === "undefined") {
        globalThis.FinalizationRegistry = function FinalizationRegistry(callback) {
            // No-op: weak ref cleanup callbacks can't fire in a single-run wasm env
        };
        globalThis.FinalizationRegistry.prototype.register = function() {};
        globalThis.FinalizationRegistry.prototype.unregister = function() {};
    }
    if (typeof globalThis.AbortController === "undefined") {
        function AbortSignal() {
            this.aborted = false;
            this.reason = undefined;
            this._listeners = [];
        }
        AbortSignal.prototype.addEventListener = function(type, fn) {
            if (type === "abort") this._listeners.push(fn);
        };
        AbortSignal.prototype.removeEventListener = function(type, fn) {
            if (type === "abort") {
                this._listeners = this._listeners.filter(function(l) { return l !== fn; });
            }
        };
        AbortSignal.prototype.throwIfAborted = function() {
            if (this.aborted) throw this.reason;
        };
        AbortSignal.abort = function(reason) {
            var s = new AbortSignal();
            s.aborted = true;
            s.reason = reason !== undefined ? reason : new Error("This operation was aborted");
            return s;
        };
        AbortSignal.timeout = function(ms) { return new AbortSignal(); };
        AbortSignal.any = function(signals) { return new AbortSignal(); };

        function AbortController() {
            this.signal = new AbortSignal();
        }
        AbortController.prototype.abort = function(reason) {
            if (this.signal.aborted) return;
            this.signal.aborted = true;
            this.signal.reason = reason !== undefined ? reason : new Error("This operation was aborted");
            var listeners = this.signal._listeners.slice();
            for (var i = 0; i < listeners.length; i++) {
                listeners[i]({ type: "abort", target: this.signal });
            }
        };

        globalThis.AbortController = AbortController;
        globalThis.AbortSignal = AbortSignal;
    }
    if (typeof globalThis.escape === "undefined") {
        globalThis.escape = function(str) {
            return String(str).replace(/[^A-Za-z0-9@*_+\-./]/g, function(ch) {
                var code = ch.charCodeAt(0);
                if (code < 256) {
                    return "%" + ("00" + code.toString(16).toUpperCase()).slice(-2);
                }
                return "%u" + ("0000" + code.toString(16).toUpperCase()).slice(-4);
            });
        };
    }
    if (typeof globalThis.unescape === "undefined") {
        globalThis.unescape = function(str) {
            return String(str)
                .replace(/%u([0-9A-Fa-f]{4})/g, function(_, hex) {
                    return String.fromCharCode(parseInt(hex, 16));
                })
                .replace(/%([0-9A-Fa-f]{2})/g, function(_, hex) {
                    return String.fromCharCode(parseInt(hex, 16));
                });
        };
    }
})();
"#
}

/// Defines the `require()` module registry and function.
///
/// Maps Node.js module specifiers to objects built from already-evaluated
/// globals. Must be evaluated AFTER all other polyfills.
pub fn require() -> &'static str {
    r#"
(function() {
    var _cache = {};

    var _modules = {
        "node:events": function() {
            var mod = globalThis.EventEmitter;
            mod.EventEmitter = mod;
            return mod;
        },
        "events": function() { return _modules["node:events"](); },
        "node:buffer": function() { return { Buffer: globalThis.Buffer }; },
        "buffer": function() { return _modules["node:buffer"](); },
        "node:url": function() {
            return { URL: globalThis.URL, URLSearchParams: globalThis.URLSearchParams };
        },
        "url": function() { return _modules["node:url"](); },
        "node:process": function() { return globalThis.process; },
        "process": function() { return globalThis.process; },
        "node:timers": function() {
            return {
                setTimeout: globalThis.setTimeout,
                clearTimeout: globalThis.clearTimeout,
                setInterval: globalThis.setInterval,
                clearInterval: globalThis.clearInterval,
                setImmediate: globalThis.setImmediate,
                clearImmediate: globalThis.clearImmediate,
            };
        },
        "timers": function() { return _modules["node:timers"](); },
        "node:timers/promises": function() {
            return {
                setTimeout: function(ms) {
                    return new Promise(function(resolve) {
                        globalThis.setTimeout(function() { resolve(); }, ms);
                    });
                },
                setImmediate: function() {
                    return new Promise(function(resolve) {
                        globalThis.setImmediate(function() { resolve(); });
                    });
                },
            };
        },
        "node:util": function() {
            return {
                deprecate: function(fn, msg) { return fn; },
                inspect: function(obj) {
                    if (obj === null) return "null";
                    if (obj === undefined) return "undefined";
                    if (typeof obj === "string") return "'" + obj + "'";
                    try { return JSON.stringify(obj); } catch(e) { return String(obj); }
                },
                inherits: function(ctor, superCtor) {
                    ctor.prototype = Object.create(superCtor.prototype, {
                        constructor: { value: ctor, writable: true, configurable: true }
                    });
                },
                format: function() {
                    var args = Array.prototype.slice.call(arguments);
                    if (args.length === 0) return "";
                    var fmt = String(args[0]);
                    var idx = 1;
                    var result = fmt.replace(/%[sdj%]/g, function(m) {
                        if (m === "%%") return "%";
                        if (idx >= args.length) return m;
                        var val = args[idx++];
                        if (m === "%s") return String(val);
                        if (m === "%d") return Number(val).toString();
                        if (m === "%j") {
                            try { return JSON.stringify(val); }
                            catch(e) { return "[Circular]"; }
                        }
                        return m;
                    });
                    while (idx < args.length) result += " " + String(args[idx++]);
                    return result;
                },
                promisify: function(fn) {
                    return function() {
                        var args = Array.prototype.slice.call(arguments);
                        return new Promise(function(resolve, reject) {
                            args.push(function(err, result) {
                                if (err) reject(err); else resolve(result);
                            });
                            fn.apply(null, args);
                        });
                    };
                },
                types: {
                    isPromise: function(v) { return v instanceof Promise; },
                    isDate: function(v) { return v instanceof Date; },
                    isRegExp: function(v) { return v instanceof RegExp; },
                },
            };
        },
        "util": function() { return _modules["node:util"](); },
        "node:path": function() {
            var path = {};
            path.sep = "/";
            path.delimiter = ":";
            path.basename = function(p, ext) {
                var base = p.split("/").filter(function(s) { return s; }).pop() || "";
                if (ext && base.endsWith(ext)) base = base.slice(0, -ext.length);
                return base;
            };
            path.dirname = function(p) {
                var parts = p.split("/"); parts.pop();
                return parts.join("/") || "/";
            };
            path.extname = function(p) {
                var base = path.basename(p);
                var idx = base.lastIndexOf(".");
                return idx > 0 ? base.slice(idx) : "";
            };
            path.join = function() {
                return Array.prototype.slice.call(arguments).join("/").replace(/\/+/g, "/");
            };
            path.resolve = function() {
                var parts = Array.prototype.slice.call(arguments);
                var resolved = "";
                for (var i = parts.length - 1; i >= 0; i--) {
                    resolved = parts[i] + "/" + resolved;
                    if (parts[i].charAt(0) === "/") break;
                }
                return "/" + resolved.replace(/\/+/g, "/").replace(/\/$/, "");
            };
            path.parse = function(p) {
                var dir = path.dirname(p);
                var base = path.basename(p);
                var ext = path.extname(p);
                var name = ext ? base.slice(0, -ext.length) : base;
                return { root: p.charAt(0) === "/" ? "/" : "", dir: dir, base: base, ext: ext, name: name };
            };
            path.isAbsolute = function(p) { return p.charAt(0) === "/"; };
            return path;
        },
        "path": function() { return _modules["node:path"](); },
        "node:crypto": function() {
            return {
                randomBytes: function(n) { return globalThis.Buffer.alloc(n); },
                randomUUID: function() { return "00000000-0000-4000-8000-000000000000"; },
                createHash: function() {
                    return {
                        update: function() { return this; },
                        digest: function(enc) {
                            return enc === "hex" ? "0".repeat(64) : globalThis.Buffer.alloc(32);
                        },
                    };
                },
                createHmac: function() {
                    return {
                        update: function() { return this; },
                        digest: function(enc) {
                            return enc === "hex" ? "0".repeat(64) : globalThis.Buffer.alloc(32);
                        },
                    };
                },
            };
        },
        "crypto": function() { return _modules["node:crypto"](); },
        "node:http": function() {
            return {
                Agent: function() {},
                request: function() { throw new Error("node:http not available in WASM"); },
                get: function() { throw new Error("node:http not available in WASM"); },
            };
        },
        "http": function() { return _modules["node:http"](); },
        "node:https": function() { return _modules["node:http"](); },
        "https": function() { return _modules["node:http"](); },
        "node:zlib": function() {
            var noop = function(buf, cb) { if (cb) cb(null, buf); return buf; };
            return {
                inflate: noop, deflate: noop,
                inflateSync: function(buf) { return buf; },
                deflateSync: function(buf) { return buf; },
                createInflate: function() {
                    return { on: function() {}, write: function() {}, end: function() {} };
                },
                createDeflate: function() {
                    return { on: function() {}, write: function() {}, end: function() {} };
                },
            };
        },
        "zlib": function() { return _modules["node:zlib"](); },
        "node:fs": function() {
            return {
                readFileSync: function() { throw new Error("fs not available in WASM"); },
                writeFileSync: function() { throw new Error("fs not available in WASM"); },
                existsSync: function() { return false; },
            };
        },
        "fs": function() { return _modules["node:fs"](); },
        "node:fs/promises": function() {
            return {
                readFile: function() { return Promise.reject(new Error("fs not available")); },
                writeFile: function() { return Promise.reject(new Error("fs not available")); },
            };
        },
        "node:os": function() {
            return {
                platform: function() { return "wasm"; },
                arch: function() { return "wasm32"; },
                cpus: function() { return []; },
                tmpdir: function() { return "/tmp"; },
                homedir: function() { return "/"; },
                EOL: "\n",
            };
        },
        "os": function() { return _modules["node:os"](); },
        "node:worker_threads": function() {
            return {
                isMainThread: true,
                parentPort: null,
                workerData: null,
                Worker: function() { throw new Error("Worker not available in WASM"); },
                SHARE_ENV: {},
            };
        },
        "worker_threads": function() { return _modules["node:worker_threads"](); },
        "node:child_process": function() {
            return {
                spawn: function() { throw new Error("child_process not available in WASM"); },
                exec: function() { throw new Error("child_process not available in WASM"); },
                fork: function() { throw new Error("child_process not available in WASM"); },
            };
        },
        "child_process": function() { return _modules["node:child_process"](); },
        "node:stream": function() {
            function Stream() { globalThis.EventEmitter.call(this); }
            Stream.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Readable = function() { globalThis.EventEmitter.call(this); };
            Stream.Readable.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Writable = function() { globalThis.EventEmitter.call(this); };
            Stream.Writable.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Duplex = function() { globalThis.EventEmitter.call(this); };
            Stream.Duplex.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.Transform = function() { globalThis.EventEmitter.call(this); };
            Stream.Transform.prototype = Object.create(globalThis.EventEmitter.prototype);
            Stream.PassThrough = Stream.Transform;
            return Stream;
        },
        "stream": function() { return _modules["node:stream"](); },
        "node:net": function() {
            function Socket() { globalThis.EventEmitter.call(this); }
            Socket.prototype = Object.create(globalThis.EventEmitter.prototype);
            Socket.prototype.connect = function() { return this; };
            Socket.prototype.write = function() { return true; };
            Socket.prototype.end = function() {};
            Socket.prototype.destroy = function() {};
            return { Socket: Socket, createConnection: function() { return new Socket(); } };
        },
        "net": function() { return _modules["node:net"](); },
        "undici": function() {
            var notAvailable = function() {
                return Promise.reject(new Error("undici not available in WASM"));
            };
            return {
                fetch: typeof globalThis.fetch === "function"
                    ? globalThis.fetch
                    : notAvailable,
                request: notAvailable,
                Agent: function() {},
                Pool: function() {},
                Client: function() {},
            };
        },
        "ws": function() {
            function WS() { globalThis.EventEmitter.call(this); }
            WS.prototype = Object.create(globalThis.EventEmitter.prototype);
            WS.prototype.send = function() {};
            WS.prototype.close = function() {};
            WS.OPEN = 1;
            WS.CLOSED = 3;
            return WS;
        },
    };

    globalThis.require = function require(name) {
        if (_cache[name]) return _cache[name];
        var factory = _modules[name];
        if (!factory) throw new Error("Cannot find module '" + name + "'");
        _cache[name] = factory();
        return _cache[name];
    };
})();
"#
}
