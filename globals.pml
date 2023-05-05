// DEFINING TYPEDEFINITIONS

typedef Content {
	mtype:url title;
	// embedded js or css files in the website
	mtype:url links[2];
}

typedef Headers {
	int code; // response code as specified in HTTP
	mtype:contentTypes contentType; // content type as specified in HTTP
	mtype:url location; // redirect url
}

typedef Response {
	byte sessionId;
	Headers headers;
	Content content;
}

typedef Request {
	mtype:url url;
	byte sessionId;
	chan browserConnection;
}

typedef Browser {
	chan queries = [1] of { mtype:query };
	chan shutdown = [1] of { bool };
	byte sessionId;
	chan connection = [10] of { Response };
	int sentPackets;
	int receivedPackets;

	bool isRunning;
	bool navigationStarted;
	bool navigationFinished;
}

// DEFINING GLOBAL VARIABLES

mtype:query = {google, yahoo, bing, custom, bad }

mtype:url = { googleCom, yahooCom, bingCom, customCom, googleJSCom, yahooJSCom, bingJSCom, customJSCom, googleCSSCom, yahooCSSCom, bingCSSCom, customCSSCom, redirect, badUrl }

mtype:contentTypes = { html, css, js, text }

// request channel for common Server that can handle 5 requests at a time
chan serverSocket = [10] of { Request }
// max 10 distinct connections to the server
bit openConnections [10];

chan serverShutdown = [1] of { int }
bool serverIsRunning;

inline prepareValidResponse(request) {
	response.sessionId = request.sessionId;
	response.headers.code = 200;

	if
	:: request.url == googleCom -> {
			url = googleCom;
			response.content.title = googleCom;
			response.content.links[0] = googleJSCom;
			response.content.links[1] = googleCSSCom;	
			
			response.headers.contentType = html;
		}
	
	:: request.url == yahooCom -> {
			url = yahooCom;
			response.content.title = yahooCom;
			response.content.links[0] = yahooJSCom;
			response.content.links[1] = yahooCSSCom;	

			response.headers.contentType = html;
		}

	:: request.url == bingCom -> {
			url = bingCom;
			response.content.title = bingCom;
			response.content.links[0] = bingJSCom;
			response.content.links[1] = bingCSSCom;	

			response.headers.contentType = html;
		}

	:: request.url == customCom -> {
			url = customCom;
			response.content.title = customCom;
			response.content.links[0] = customJSCom;
			response.content.links[1] = customCSSCom;	

			response.headers.contentType = html;
		}

	:: request.url == googleJSCom -> {
			url = googleJSCom;
			response.headers.contentType = js;
		}

	:: request.url == yahooJSCom -> {
			url = yahooJSCom;
			response.headers.contentType = js;
		}

	:: request.url == bingJSCom -> {
			url = bingJSCom;
			response.headers.contentType = js;
		}

	:: request.url == customJSCom -> {
			url = customJSCom;
			response.headers.contentType = js;
		}

	:: request.url == googleCSSCom -> {
			url = googleCSSCom;
			response.headers.contentType = css;
		}

	:: request.url == yahooCSSCom -> {
			url = yahooCSSCom;
			response.headers.contentType = css;
		}

	:: request.url == bingCSSCom -> {
			url = bingCSSCom;
			response.headers.contentType = css;
		}

	:: request.url == customCSSCom -> {
			url = customCSSCom;
			response.headers.contentType = css;
		}

	:: {
			printf("[runServer]: Unknown error on the server\n");
			url = badUrl;
			response.sessionId = request.sessionId;
			response.headers.code = 500;
			response.headers.contentType = html;
		}
	fi
}

// always active listening for requests
// need a mechanism to prevent infinite loop
active proctype runServer() {
	Request request;
	Response response;
	mtype:url url;
	mtype:server serverRequest;
	int sessionId;

	serverIsRunning = true;

	do 
		:: serverSocket?request -> {
				// open connection
				openConnections[request.sessionId] = 1;

				// non deterministically choose what to response
				if
					:: prepareValidResponse(request);

					:: {
							response.sessionId = request.sessionId;
							response.headers.code = 301;
							response.headers.contentType = html;

							// make random redirect
							if
								:: response.headers.location = googleCom;
								:: response.headers.location = yahooCom;
								:: response.headers.location = bingCom;
								:: response.headers.location = customCom;
							fi
							response.content.title = response.headers.location;

							printf("[runServer]: Received request from %e that needs to be redirected to %e\n", request.url, response.headers.location)
					}
					
				fi

				request.browserConnection!response;
				printf("[runServer]: Sent response from %e to browser %d\n", request.url, request.sessionId)
			}

		:: serverShutdown?sessionId -> {
				openConnections[sessionId] = 0;
				printf("[runServer]: Browser %d is shutting down\n", sessionId);

				// check if there are no more open connections
				int i;
				bool noConnections = true;
				for (i : 0 .. 9) {
					if
						:: openConnections[i] == 1 -> {
								noConnections = false;
								break;
							}
						:: else -> skip;
					fi
				}

				if 
					:: noConnections -> {
							printf("[runServer]: Server shutting down\n");
							serverIsRunning = false;
							break;
						}
					:: else -> skip;
				fi
			}

		// // shutdown server if there are no requests
		// :: timeout -> {
		// 		printf("Server shutting down\n");
		// 		break;
		// 	}
	od
}

// dummy init process
init {
	printf("");
}