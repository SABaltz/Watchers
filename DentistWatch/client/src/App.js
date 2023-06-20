import React from "react";
import {BrowserRouter, Route, Routes} from "react-router-dom";
import NavBar from "./components/NavBar";
import Footer from "./components/Footer";
import HomePage from "./components/HomePage";
import AddEntry from "./components/AddEntry";

function App() {
    return (
        <>
            <NavBar/>
            <BrowserRouter>
                <Routes>
                    <Route exact path="/" element={<HomePage/>}/>
                    <Route path="/add" element={<AddEntry/>}/>
                </Routes>
            </BrowserRouter>
            <Footer/>
        </>
    );
}

export default App;
