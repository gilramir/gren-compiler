// The Geng backends on a stack of their own (geng-lang m3-sweep.md D645).
//
// The C and BEAM backends are Geng in this bundle, and they recurse once for
// each level of the Core they read, lower and print: node's default stack,
// about 1 MB, held a Core term about 1,000 deep (§SW30 item 1). Node takes no
// larger stack for its main thread without a flag and an operating-system stack
// to match, but a worker thread's is what `resourceLimits.stackSizeMb` asks for.
// So the backend runs in a worker started on this same file, which `main` sees
// as a request (`request`) and answers once (`answer`); the command line, its
// terminal and its reports stay on the main thread.

var worker_threads = require("node:worker_threads");

// The request this thread was started with, or "" on the main thread.
function request(succeed, fail) {
  var data = worker_threads.workerData;
  succeed(
    !worker_threads.isMainThread && data && typeof data.gengBackend === "string"
      ? data.gengBackend
      : "",
  );
}

// The answer, to the thread that started this one.
function answer(text, succeed, fail) {
  worker_threads.parentPort.postMessage(text);
  succeed({});
}

// A worker on this file with a stack of `stackMb` MiB, handed `text`; the task
// succeeds with its answer, and fails with why when it ends without one: a
// crash, which it has written on standard error, or a worker node could not
// start.
function run(stackMb, text, succeed, fail) {
  var worker;
  try {
    worker = new worker_threads.Worker(module.filename, {
      workerData: { gengBackend: text },
      resourceLimits: { stackSizeMb: stackMb },
    });
  } catch (e) {
    fail(String((e && e.message) || e));
    return;
  }
  var done = false;
  worker.on("message", function (message) {
    if (!done) {
      done = true;
      succeed(String(message));
    }
  });
  worker.on("error", function (e) {
    if (!done) {
      done = true;
      fail(String((e && e.message) || e));
    }
  });
  worker.on("exit", function (code) {
    if (!done) {
      done = true;
      fail("it ended with status " + code + " and no answer");
    }
  });
}
