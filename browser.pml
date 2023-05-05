#include "globals.pml"

Browser browser1;
Browser browser2;

// check that browser always receives the same number of packets that it sends
ltl prop1 { []((browser1.receivedPackets != browser1.sentPackets) -> <>(browser1.receivedPackets == browser1.sentPackets)) }

// check that server is running if at least one browser is running
ltl prop2 { [](browser1.isRunning || browser2.isRunning -> serverIsRunning) }

// check that server is not running if no browser is running - Must be failed, because server can be running even if no browser is running
ltl prop3 { [](!browser1.isRunning && !browser2.isRunning -> !serverIsRunning) }

// check that browser always finishes navigation if it starts navigation
ltl prop4 { [](browser1.navigationStarted -> browser1.navigationFinished) }

// check that browser always starts navigation if it is running
ltl prop5 { [](browser1.navigationStarted -> browser1.isRunning) }

// check that it is not always the case that browser starts navigation if it is running
ltl prop6 { [](browser1.isRunning -> !browser1.navigationStarted) }

inline sendUrlRequest(url, browser) {
	printf("[sendUrlRequest]: Browser %d: Checking if %e is already cached\n", browser.sessionId, url)
	if
		:: {
				printf("[sendUrlRequest]: Browser %d: %e is not cached\n", browser.sessionId, url)
				printf("[sendUrlRequest]: Browser %d: Sending request to %e\n", browser.sessionId, url)
				Request request;
				request.sessionId = browser.sessionId;
				request.browserConnection = browser.connection;
				request.url = url;
				serverSocket!request;
				browser.sentPackets++;
				browser.navigationStarted = true;
		}

		:: {
				printf("[sendUrlRequest]: Browser %d: %e is cached\n", browser.sessionId, url);
				printf("[sendUrlRequest]: Browser %d: Navigation in %e ends\n", browser.sessionId, url)
				browser.navigationFinished = true;
		}
	fi
}

inline receiveUrlResponse(response, browser) {
	printf("[receiveUrlResponse]: Browser %d: Received response %d from %e\n", browser.sessionId, response.headers.code, response.content.title);
	
	if
		:: response.headers.code == 301 -> {
				// redirection
				printf("[receiveUrlResponse]: Browser %d: %e is redirecting\n", browser.sessionId, response.content.title);
				url = response.headers.location;
				sendUrlRequest(url, browser)
		}

		:: response.headers.contentType != html && response.headers.code == 200 -> {
				// not html
				printf("[receiveUrlResponse]: Browser %d: response from %e is not html\n", browser.sessionId, response.content.title);
				printf("[receiveUrlResponse]: Browser %d: navigation in %e ends\n", browser.sessionId, response.content.title)
				browser.navigationFinished = true;
		}

		:: response.headers.contentType == html && response.headers.code == 200 -> {
				// html and 200
				// The network process continues navigation.
				printf("[receiveUrlResponse]: Browser %d: received html packet from %e successfully\n", browser.sessionId, response.content.title);

				// parse html
				url = response.content.links[0];
				sendUrlRequest(url, browser)
				url = response.content.links[1];
				sendUrlRequest(url, browser)
				browser.navigationFinished = true;
		}

		:: else -> {
				printf("[receiveUrlResponse]: Browser %d: received bad response from %e\n", browser.sessionId, response.content.title);
				printf("[receiveUrlResponse]: Browser %d: navigation in %e ends\n", browser.sessionId, response.content.title)
				browser.navigationFinished = true;
		}
	fi
}

inline handleUserInput(query, browser) {
	// take query from the search input and decide whether it is a query or a url
	// if it is a url then send it to the server
	// otherwise, construct a url and send it to the server
	printf("[handleUserInput]: User input: %e\n", query)

	mtype:url url;

	if
		// if the user input is a bad query
		:: query == bad -> {
				printf("[handleUserInput]: Bad query\n");
		}

		:: else {
			if
				:: query == google -> url = googleCom;
				:: query == yahoo -> url = yahooCom;
				:: query == bing -> url = bingCom;
				
				// if the user input is not a url then construct a url
				:: query == custom -> url = customCom;
			fi

			sendUrlRequest(url, browser);
		}
	fi

}

proctype runBrowser(Browser browser) {
	mtype:query query;
	chan queries = browser.queries;
	Response response;
	browser.isRunning = true;

	// generate a random number to be used as a session id
	int random;

	GEN_SESSION_ID:
		select(random : 0 .. 9);

		if 
			:: openConnections[random] == 1 -> {
				goto GEN_SESSION_ID;
			}

			:: else -> {
				browser.sessionId = random;
			}
		fi
	
	do 
		:: queries?query -> {
				printf("[runBrowser]: Browser %d: User typed a query: %e\n", browser.sessionId, query);
				handleUserInput(query, browser);
			}

		:: browser.connection?response -> {
				browser.receivedPackets++;
				receiveUrlResponse(response, browser)
			}

		:: browser.shutdown?true -> {
			// wait till all the requests will response
				do
					:: browser.receivedPackets != browser.sentPackets -> {
							browser.connection?response;
							browser.receivedPackets++;
							receiveUrlResponse(response, browser)
						}
					:: else -> break;
				od

				printf("[runBrowser]: Browser %d is shutting down\n", browser.sessionId);
				browser.isRunning = false;

				printf("[runBrowser]: Sending signal to shutdown server\n");
				serverShutdown!browser.sessionId;
				break;
			}
	od
}

proctype doSomeHumanInteractions(Browser browser) {
	// send at least N queries and then shutdown
	int i = 0;
	int N = 10;
	do
		// suppose a user is typing in a search input
		:: {
			if
				:: browser.queries!google;
				:: browser.queries!yahoo;
				:: browser.queries!bing;
				:: browser.queries!custom;
				:: browser.queries!bad;
			fi 

			i++;
		}
	
		:: { 
			if
			  :: i < N -> skip;
			  :: i >= N -> browser.shutdown!true; break;
			fi
		 }
	od
}

init {
	run runBrowser(browser1)
	run doSomeHumanInteractions(browser1)

	run runBrowser(browser2)
	run doSomeHumanInteractions(browser2)
}