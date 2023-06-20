import React from "react";
import {BrowserRouter, Routes} from "react-router-dom";
import NavBar from "./components/NavBar";
import Footer from "./components/Footer";

function App() {
    return (
        <>
            <NavBar/>
            <BrowserRouter>
                <Routes>
                    {/*<Route exact path="/" element={<RecordList />} />*/}
                    {/*<Route path="/edit/:id" element={<Edit />} />*/}
                    {/*<Route path="/create" element={<Create />} />*/}
                </Routes>
            </BrowserRouter>
            <Footer/>
        </>
    );
}

export default App;
