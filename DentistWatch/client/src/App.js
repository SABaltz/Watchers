import React from "react";
import {BrowserRouter, Route, Routes} from "react-router-dom";
import NavBar from "./components/NavBar";
import Footer from "./components/Footer";
import HomePage from "./components/HomePage";
import Report from "./components/Report";
import List from "./components/List";

function App() {
    return (
        <>
            <NavBar/>
            <BrowserRouter>
                <Routes>
                    <Route exact path="/" element={<HomePage/>}/>
                    <Route path="/report" element={<Report/>}/>
                    <Route path="/list" element={<List/>}/>
                </Routes>
            </BrowserRouter>
            <Footer/>
        </>
    );
}

export default App;
