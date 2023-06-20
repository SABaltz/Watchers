import React from "react";
import { BrowserRouter } from "react-router-dom";

function App() {
    return (
        <BrowserRouter>
            <Routes>
                {/*<Route exact path="/" element={<RecordList />} />*/}
                {/*<Route path="/edit/:id" element={<Edit />} />*/}
                {/*<Route path="/create" element={<Create />} />*/}
            </Routes>
        </BrowserRouter>
    );
}

export default App;
